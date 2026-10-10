import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# Rank-gap tail integration

This module contains the measure-theoretic algebra used after a conditional tail estimate has
been established.  It proves the threshold integral, converts an exponential tail bound into a
second-moment bound, and gives a finite-family Fubini form.  No counting-process occupation
estimate or stopped matching theorem is assumed here.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace OTSelector

/-! ### Elementary threshold and exponential integrals -/

/-- The threshold part of the layer-cake integral.

The endpoint convention is immaterial for Lebesgue integration; using `≤` makes the interval
reduction exact.  In applications the strict indicator `K > c * r` is bounded by this one.
-/
theorem integral_two_mul_threshold_le {a : ℝ} (ha : 0 ≤ a) :
    ∫ r : ℝ in Ioi 0, (2 : ℝ) * r * (if r ≤ a then 1 else 0) = a ^ 2 := by
  have hfun : (fun r : ℝ => (2 : ℝ) * r * (if r ≤ a then 1 else 0)) =
      Set.indicator (Iic a) (fun r : ℝ => (2 : ℝ) * r) := by
    funext r
    by_cases hr : r ≤ a <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hr]
  rw [hfun, setIntegral_indicator measurableSet_Iic]
  have hset : Ioi (0 : ℝ) ∩ Iic a = Ioc 0 a := by
    ext r
    simp only [mem_inter_iff, mem_Ioi, mem_Iic, mem_Ioc]
  rw [hset, ← intervalIntegral.integral_of_le ha]
  rw [intervalIntegral.integral_const_mul, integral_id]
  ring

/- The same threshold calculation in the nonnegative Lebesgue-integral form. -/
private theorem lintegral_threshold_weight {a : ℝ} (ha : 0 ≤ a) :
    ∫⁻ r : ℝ in Ioi 0, ENNReal.ofReal (r * (if r ≤ a then 1 else 0)) =
      ENNReal.ofReal (a ^ 2 / 2) := by
  have hfun : (fun r : ℝ => ENNReal.ofReal (r * (if r ≤ a then 1 else 0))) =
      Set.indicator (Iic a) (fun r : ℝ => ENNReal.ofReal r) := by
    funext r
    by_cases hr : r ≤ a
    · simp [Set.indicator_of_mem, hr]
    · simp [Set.indicator_of_notMem, hr]
  rw [hfun, setLIntegral_indicator measurableSet_Iic]
  have hset : Ioi (0 : ℝ) ∩ Iic a = Ioc 0 a := by
    ext r
    simp only [mem_inter_iff, mem_Ioi, mem_Iic, mem_Ioc]
  rw [show Iic a ∩ Ioi (0 : ℝ) = Ioc 0 a by simpa [inter_comm] using hset]
  have hbase : IntegrableOn (fun r : ℝ => r) (Ioc 0 a) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le ha]
    exact continuousOn_id.intervalIntegrable
  have hreal : (∫ r : ℝ in Ioc 0 a, r) = a ^ 2 / 2 := by
    rw [← intervalIntegral.integral_of_le ha, integral_id]
    ring
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) a)] (fun r ↦ r) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with r hr
    exact (mem_Ioc.mp hr).1.le
  rw [← hreal]
  exact (ofReal_integral_eq_lintegral_ofReal hbase hnn).symm

private theorem lintegral_exp_weight {d : ℝ} (hd : 0 < d) :
    ∫⁻ r : ℝ in Ioi 0, ENNReal.ofReal (r * Real.exp (-d * r)) =
      ENNReal.ofReal ((1 / d) ^ 2) := by
  have hbase : IntegrableOn (fun r : ℝ => r * Real.exp (-d * r)) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (1 : ℝ))
      (p := (1 : ℝ)) (b := d) (by norm_num) (by norm_num) hd
    refine h.congr_fun ?_ measurableSet_Ioi
    intro r hr
    simp [Real.rpow_one]
  have hreal : (∫ r : ℝ in Ioi 0, r * Real.exp (-d * r)) = (1 / d) ^ 2 := by
    simpa [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, mul_comm] using
      (Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (2 : ℝ)) (r := d)
        (by norm_num) hd)
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun r ↦ r * Real.exp (-d * r)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    exact mul_nonneg (mem_Ioi.mp hr).le (Real.exp_pos _).le
  rw [← hreal]
  exact (ofReal_integral_eq_lintegral_ofReal hbase hnn).symm

/-! ### The weighted tail integral -/

/-- The weighted integral of a threshold indicator plus an exponential tail, with the exact
constant used by the conditional second-moment theorem below. -/
theorem lintegral_tail_weight_le {K c C d : ℝ} (hK : 0 ≤ K) (hc : 0 < c)
    (hC : 0 ≤ C) (hd : 0 < d) :
    ∫⁻ r : ℝ in Ioi 0,
        ENNReal.ofReal (((if K > c * r then (1 : ℝ) else 0) + C * Real.exp (-d * r)) * r) ≤
      ENNReal.ofReal ((K / c) ^ 2 / 2 + C / d ^ 2) := by
  let a : ℝ := K / c
  let f : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (r * (if r ≤ a then (1 : ℝ) else 0))
  let g : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (C * (r * Real.exp (-d * r)))
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity
  have hf_meas : Measurable f := by
    let hi : Measurable (fun r : ℝ => if r ≤ a then (1 : ℝ) else 0) :=
      Measurable.ite (measurableSet_le measurable_id measurable_const)
        measurable_const measurable_const
    exact (measurable_id.mul hi).ennreal_ofReal
  have hg_meas : Measurable g := by
    let hm : Measurable (fun r : ℝ => r * Real.exp (-d * r)) := by
      have hneg : Measurable (fun r : ℝ => -d * r) :=
        (measurable_const (a := -d)).mul measurable_id
      exact measurable_id.mul hneg.exp
    exact ((measurable_const (a := C)).mul hm).ennreal_ofReal
  have hpoint : ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (((if K > c * r then (1 : ℝ) else 0) + C * Real.exp (-d * r)) * r) ≤
        f r + g r := by
    intro r hr
    have hthreshold : (if K > c * r then (1 : ℝ) else 0) ≤
        if r ≤ a then (1 : ℝ) else 0 := by
      by_cases hkr : K > c * r
      · have hr_a : r ≤ a := by
          dsimp [a]
          apply (le_div_iff₀ hc).2
          nlinarith
        simp [hkr, hr_a]
      · simp [hkr]
        split_ifs <;> positivity
    have hq : 0 ≤ (if K > c * r then (1 : ℝ) else 0) + C * Real.exp (-d * r) := by
      positivity
    have hu : 0 ≤ r * (if r ≤ a then (1 : ℝ) else 0) := by
      positivity
    have hv : 0 ≤ C * (r * Real.exp (-d * r)) := by
      positivity
    rw [show f r = ENNReal.ofReal (r * (if r ≤ a then (1 : ℝ) else 0)) by rfl,
      show g r = ENNReal.ofReal (C * (r * Real.exp (-d * r))) by rfl,
      ← ENNReal.ofReal_add hu hv]
    apply ENNReal.ofReal_le_ofReal
    calc
      ((if K > c * r then (1 : ℝ) else 0) + C * Real.exp (-d * r)) * r ≤
          (if r ≤ a then (1 : ℝ) else 0) * r + C * (r * Real.exp (-d * r)) := by
            calc
              _ = (if K > c * r then (1 : ℝ) else 0) * r +
                  C * Real.exp (-d * r) * r := by ring
              _ ≤ (if r ≤ a then (1 : ℝ) else 0) * r +
                  C * Real.exp (-d * r) * r := by
                exact add_le_add (mul_le_mul_of_nonneg_right hthreshold hr.le) le_rfl
              _ = _ := by ring
      _ = r * (if r ≤ a then (1 : ℝ) else 0) + C * (r * Real.exp (-d * r)) := by ring
  have hfi : ∫⁻ r : ℝ in Ioi 0, f r = ENNReal.ofReal (a ^ 2 / 2) := by
    dsimp [f]
    simpa using lintegral_threshold_weight ha
  have hgi : ∫⁻ r : ℝ in Ioi 0, g r = ENNReal.ofReal (C / d ^ 2) := by
    dsimp [g]
    rw [show (fun r : ℝ => ENNReal.ofReal (C * (r * Real.exp (-d * r)))) =
        (fun r : ℝ => ENNReal.ofReal C * ENNReal.ofReal (r * Real.exp (-d * r))) by
      funext r
      rw [← ENNReal.ofReal_mul hC]]
    rw [lintegral_const_mul' (ENNReal.ofReal C) _ ENNReal.ofReal_ne_top]
    rw [lintegral_exp_weight hd]
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ C)]
    congr 1
    field_simp [hd.ne']
  have hmono : ∫⁻ r : ℝ in Ioi 0,
      ENNReal.ofReal (((if K > c * r then (1 : ℝ) else 0) + C * Real.exp (-d * r)) * r) ≤
        ∫⁻ r : ℝ in Ioi 0, f r + g r := by
    apply setLIntegral_mono_ae
    · exact (hf_meas.add hg_meas).aemeasurable
    · exact Filter.Eventually.of_forall (fun r hr => hpoint r (mem_Ioi.mp hr))
  calc
    _ ≤ ∫⁻ r : ℝ in Ioi 0, f r + g r := hmono
    _ = (∫⁻ r : ℝ in Ioi 0, f r) + ∫⁻ r : ℝ in Ioi 0, g r := by
      simpa only using
        (lintegral_add_left' (μ := volume.restrict (Ioi 0)) hf_meas.aemeasurable g)
    _ = ENNReal.ofReal (a ^ 2 / 2) + ENNReal.ofReal (C / d ^ 2) := by rw [hfi, hgi]
    _ = ENNReal.ofReal ((K / c) ^ 2 / 2 + C / d ^ 2) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity)]

/-! ### Conditional bounds through measurable-set integrals -/

/-- An integrable `m`-measurable function bounds a conditional expectation almost everywhere
exactly when it bounds the integral of the original function on every `m`-measurable set.

The reverse implication is proved on `μ.trim hm`, where those sets form the ambient measurable
space.  This formulation is useful when a continuum of conditional estimates must be integrated:
one fixes the measurable set first and never chooses a common exceptional set.
-/
theorem condExp_le_iff_forall_setIntegral_le
    {Ω : Type*} [m₀ : MeasurableSpace Ω] {m : MeasurableSpace Ω}
    {μ : @Measure Ω m₀} [IsFiniteMeasure μ] (hm : m ≤ m₀) {f g : Ω → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) (hgm : StronglyMeasurable[m] g) :
    μ[f | m] ≤ᵐ[μ] g ↔
      ∀ A : Set Ω, MeasurableSet[m] A →
        (∫ ω in A, f ω ∂μ) ≤ ∫ ω in A, g ω ∂μ := by
  constructor
  · intro hfg A hA
    rw [← setIntegral_condExp hm hf hA]
    exact integral_mono_ae integrable_condExp.integrableOn hg.integrableOn
      (ae_restrict_le hfg)
  · intro hset
    have hce_meas : StronglyMeasurable[m] (μ[f | m]) :=
      stronglyMeasurable_condExp
    have hce_trim : Integrable (μ[f | m]) (μ.trim hm) :=
      integrable_condExp.trim hm hce_meas
    have hg_trim : Integrable g (μ.trim hm) := hg.trim hm hgm
    apply ae_le_of_ae_le_trim
    apply ae_le_of_forall_setIntegral_le hce_trim hg_trim
    intro A hA _hAfinite
    rw [← setIntegral_trim hm hce_meas hA, ← setIntegral_trim hm hgm hA,
      setIntegral_condExp hm hf hA]
    exact hset A hA

/-- Set-integral layer-cake form of a conditional tail estimate.

For every `m`-measurable `A`, the conditional tail hypothesis is first integrated over `A`.
Tonelli is then applied to the resulting scalar inequalities.  Thus the hypothesis may have a
different almost-everywhere exceptional set for every threshold `r`.
-/
theorem setLIntegral_sq_le_of_condExp_tail
    {Ω : Type*} [m₀ : MeasurableSpace Ω] {m : MeasurableSpace Ω}
    {μ : @Measure Ω m₀} [IsFiniteMeasure μ] (hm : m ≤ m₀)
    (X K : Ω → ℝ) (hX_meas : Measurable[m₀] X) (hX_nonneg : ∀ ω, 0 ≤ X ω)
    (hK_meas : StronglyMeasurable[m] K) (hK_nonneg : ∀ ω, 0 ≤ K ω)
    {c C d : ℝ} (hc : 0 < c) (hC : 0 ≤ C) (hd : 0 < d)
    (hTail : ∀ r : ℝ, 0 < r →
      μ[({ω | r < X ω}.indicator (fun _ ↦ (1 : ℝ))) | m] ≤ᵐ[μ]
        fun ω ↦ (if K ω > c * r then (1 : ℝ) else 0) + C * Real.exp (-d * r))
    (A : Set Ω) (hA : MeasurableSet[m] A) :
    ∫⁻ ω in A, ENNReal.ofReal (X ω ^ (2 : ℕ)) ∂μ ≤
      ∫⁻ ω in A, ENNReal.ofReal ((K ω / c) ^ 2 + 2 * C / d ^ 2) ∂μ := by
  let _ : MeasurableSpace Ω := m₀
  let B : ℝ → Ω → ℝ := fun r ω ↦
    (if K ω > c * r then (1 : ℝ) else 0) + C * Real.exp (-d * r)
  let F : ℝ → Ω → ℝ≥0∞ := fun r ω ↦ ENNReal.ofReal (B r ω * r)
  have hK_meas₀ : Measurable[m₀] K := (hK_meas.mono hm).measurable
  have hB_nonneg : ∀ r ω, 0 ≤ B r ω := by
    intro r ω
    dsimp [B]
    positivity
  have htail_measure : ∀ r : ℝ, 0 < r →
      (μ.restrict A) {ω | r < X ω} ≤
        ∫⁻ ω in A, ENNReal.ofReal (B r ω) ∂μ := by
    intro r hr
    have hE : MeasurableSet[m₀] {ω | r < X ω} :=
      measurableSet_lt measurable_const hX_meas
    have hI_int : Integrable ({ω | r < X ω}.indicator (fun _ ↦ (1 : ℝ))) μ :=
      (integrable_const (1 : ℝ)).indicator hE
    have hKset : MeasurableSet[m₀] {ω | K ω > c * r} :=
      measurableSet_lt measurable_const hK_meas₀
    have hB_meas : Measurable[m₀] (B r) := by
      dsimp [B]
      exact (Measurable.ite hKset measurable_const measurable_const).add measurable_const
    have hB_int : Integrable (B r) μ := by
      apply Integrable.of_bound hB_meas.aestronglyMeasurable
        (1 + C * Real.exp (-d * r))
      filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (hB_nonneg r ω)]
      dsimp [B]
      by_cases hω : K ω > c * r <;> simp [hω]
    have hmono :
        (∫ ω in A,
            μ[({ω | r < X ω}.indicator (fun _ ↦ (1 : ℝ))) | m] ω ∂μ) ≤
          ∫ ω in A, B r ω ∂μ := by
      apply integral_mono_ae integrable_condExp.integrableOn hB_int.integrableOn
      have ht := hTail r hr
      change μ[({ω | r < X ω}.indicator (fun _ ↦ (1 : ℝ))) | m] ≤ᵐ[μ] B r at ht
      exact ae_restrict_le ht
    rw [setIntegral_condExp hm hI_int hA] at hmono
    have hreal : (μ.restrict A).real {ω | r < X ω} ≤
        ∫ ω in A, B r ω ∂μ := by
      have hindicator := integral_indicator_one (μ := μ.restrict A) hE
      change (∫ ω in A, {ω | r < X ω}.indicator (fun _ ↦ (1 : ℝ)) ω ∂μ) =
        (μ.restrict A).real {ω | r < X ω} at hindicator
      exact hindicator ▸ hmono
    calc
      (μ.restrict A) {ω | r < X ω} =
          ENNReal.ofReal ((μ.restrict A).real {ω | r < X ω}) := by
            rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
      _ ≤ ENNReal.ofReal (∫ ω in A, B r ω ∂μ) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = ∫⁻ ω in A, ENNReal.ofReal (B r ω) ∂μ :=
        ofReal_integral_eq_lintegral_ofReal hB_int.integrableOn
          (Filter.Eventually.of_forall (hB_nonneg r))
  have hF_meas : Measurable[(inferInstance : MeasurableSpace ℝ).prod m₀]
      (Function.uncurry F) := by
    have hthreshold : Measurable[(inferInstance : MeasurableSpace ℝ).prod m₀]
        (fun z : ℝ × Ω ↦
        if K z.2 > c * z.1 then (1 : ℝ) else 0) :=
      Measurable.ite
        (measurableSet_lt (measurable_const.mul measurable_fst)
          (hK_meas₀.comp measurable_snd))
        measurable_const measurable_const
    have hexp : Measurable[(inferInstance : MeasurableSpace ℝ).prod m₀]
        (fun z : ℝ × Ω ↦ Real.exp (-d * z.1)) :=
      (measurable_const.mul measurable_fst).exp
    change Measurable[(inferInstance : MeasurableSpace ℝ).prod m₀] (fun z : ℝ × Ω ↦
      ENNReal.ofReal
        (((if K z.2 > c * z.1 then (1 : ℝ) else 0) + C * Real.exp (-d * z.1)) * z.1))
    exact (hthreshold.add (measurable_const.mul hexp)).mul measurable_fst |>.ennreal_ofReal
  have htail_weighted :
      ∫⁻ r : ℝ in Ioi 0,
          (μ.restrict A) {ω | r < X ω} * ENNReal.ofReal r ≤
        ∫⁻ r : ℝ in Ioi 0, ∫⁻ ω in A, F r ω ∂μ := by
    apply lintegral_mono_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    calc
      (μ.restrict A) {ω | r < X ω} * ENNReal.ofReal r ≤
          (∫⁻ ω in A, ENNReal.ofReal (B r ω) ∂μ) * ENNReal.ofReal r :=
        mul_le_mul_left (htail_measure r (mem_Ioi.mp hr)) _
      _ ≤ ∫⁻ ω in A, ENNReal.ofReal (B r ω) * ENNReal.ofReal r ∂μ :=
        lintegral_mul_const_le _ _
      _ = ∫⁻ ω in A, F r ω ∂μ := by
        apply lintegral_congr
        intro ω
        dsimp [F]
        rw [← ENNReal.ofReal_mul (hB_nonneg r ω)]
  have hswap :
      (∫⁻ r : ℝ in Ioi 0, ∫⁻ ω in A, F r ω ∂μ) =
        ∫⁻ ω in A, (∫⁻ r : ℝ in Ioi 0, F r ω) ∂μ := by
    exact lintegral_lintegral_swap
      (μ := volume.restrict (Ioi (0 : ℝ))) (ν := μ.restrict A) hF_meas.aemeasurable
  have hdouble :
      (∫⁻ r : ℝ in Ioi 0, ∫⁻ ω in A, F r ω ∂μ) ≤
        ∫⁻ ω in A, ENNReal.ofReal ((K ω / c) ^ 2 / 2 + C / d ^ 2) ∂μ := by
    rw [hswap]
    apply lintegral_mono
    intro ω
    simpa only [F, B] using
      lintegral_tail_weight_le (K := K ω) (hK_nonneg ω) hc hC hd
  have hX_nonneg_A : 0 ≤ᵐ[μ.restrict A] X :=
    Filter.Eventually.of_forall hX_nonneg
  have hX_ae_A : AEMeasurable X (μ.restrict A) := hX_meas.aemeasurable
  have hlayer := lintegral_rpow_eq_lintegral_meas_lt_mul (μ.restrict A)
    hX_nonneg_A hX_ae_A
      (p := (2 : ℝ)) (by norm_num)
  have hlayer' :
      ∫⁻ ω in A, ENNReal.ofReal (X ω ^ (2 : ℕ)) ∂μ =
        ENNReal.ofReal (2 : ℝ) *
          ∫⁻ r : ℝ in Ioi 0,
            (μ.restrict A) {ω | r < X ω} * ENNReal.ofReal r := by
    simpa [Real.rpow_natCast, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one] using hlayer
  calc
    ∫⁻ ω in A, ENNReal.ofReal (X ω ^ (2 : ℕ)) ∂μ =
        ENNReal.ofReal (2 : ℝ) *
          ∫⁻ r : ℝ in Ioi 0,
            (μ.restrict A) {ω | r < X ω} * ENNReal.ofReal r := hlayer'
    _ ≤ ENNReal.ofReal (2 : ℝ) *
        ∫⁻ ω in A, ENNReal.ofReal ((K ω / c) ^ 2 / 2 + C / d ^ 2) ∂μ := by
      exact mul_le_mul_of_nonneg_left (htail_weighted.trans hdouble) (by positivity)
    _ = ∫⁻ ω in A, ENNReal.ofReal ((K ω / c) ^ 2 + 2 * C / d ^ 2) ∂μ := by
      rw [← lintegral_const_mul' (μ := μ.restrict A) (ENNReal.ofReal (2 : ℝ))
        (fun ω ↦ ENNReal.ofReal ((K ω / c) ^ 2 / 2 + C / d ^ 2))
        ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro ω
      rw [← ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ))]
      congr 1
      ring

/-- A conditional threshold-plus-exponential tail bound gives both square integrability and the
sharp conditional second-moment estimate.  No square-integrability assumption on `X` is used.
-/
theorem integrable_sq_and_condExp_sq_le_of_tail
    {Ω : Type*} [m₀ : MeasurableSpace Ω] {m : MeasurableSpace Ω}
    {μ : @Measure Ω m₀} [IsFiniteMeasure μ] (hm : m ≤ m₀)
    (X K : Ω → ℝ) (hX_meas : Measurable[m₀] X) (hX_nonneg : ∀ ω, 0 ≤ X ω)
    (hK_meas : StronglyMeasurable[m] K) (hK_nonneg : ∀ ω, 0 ≤ K ω)
    (hK_sq_int : Integrable (fun ω ↦ K ω ^ (2 : ℕ)) μ)
    {c C d : ℝ} (hc : 0 < c) (hC : 0 ≤ C) (hd : 0 < d)
    (hTail : ∀ r : ℝ, 0 < r →
      μ[({ω | r < X ω}.indicator (fun _ ↦ (1 : ℝ))) | m] ≤ᵐ[μ]
        fun ω ↦ (if K ω > c * r then (1 : ℝ) else 0) + C * Real.exp (-d * r)) :
    Integrable (fun ω ↦ X ω ^ (2 : ℕ)) μ ∧
      μ[(fun ω ↦ X ω ^ (2 : ℕ)) | m] ≤ᵐ[μ]
        fun ω ↦ (K ω / c) ^ 2 + 2 * C / d ^ 2 := by
  let _ : MeasurableSpace Ω := m₀
  let Y : Ω → ℝ := fun ω ↦ X ω ^ (2 : ℕ)
  let R : Ω → ℝ := fun ω ↦ (K ω / c) ^ 2 + 2 * C / d ^ 2
  have hY_meas : Measurable[m₀] Y := by
    exact hX_meas.pow measurable_const
  have hY_nonneg : ∀ ω, 0 ≤ Y ω := by
    intro ω
    exact sq_nonneg (X ω)
  have hKdiv_meas : StronglyMeasurable[m] (fun ω ↦ K ω / c) :=
    (hK_meas.measurable.div_const c).stronglyMeasurable
  have hR_meas : StronglyMeasurable[m] R := by
    exact (hKdiv_meas.pow 2).add stronglyMeasurable_const
  have hKterm_int : Integrable (fun ω ↦ (K ω / c) ^ 2) μ := by
    have hscaled := hK_sq_int.const_mul (c⁻¹ ^ 2)
    apply hscaled.congr
    filter_upwards with ω
    calc
      c⁻¹ ^ 2 * K ω ^ 2 = (K ω * c⁻¹) ^ 2 := by ring
      _ = (K ω / c) ^ 2 := by rw [div_eq_mul_inv]
  have hR_int : Integrable R μ := by
    exact hKterm_int.add (integrable_const (2 * C / d ^ 2))
  have hR_nonneg : ∀ ω, 0 ≤ R ω := by
    intro ω
    dsimp [R]
    positivity
  have hsetL : ∀ A : Set Ω, MeasurableSet[m] A →
      ∫⁻ ω in A, ENNReal.ofReal (Y ω) ∂μ ≤
        ∫⁻ ω in A, ENNReal.ofReal (R ω) ∂μ := by
    intro A hA
    simpa only [Y, R] using
      setLIntegral_sq_le_of_condExp_tail (m := m) (μ := μ) hm X K hX_meas
        hX_nonneg hK_meas hK_nonneg hc hC hd hTail A hA
  have hR_finite : ∫⁻ ω, ENNReal.ofReal (R ω) ∂μ < ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hR_int
      (Filter.Eventually.of_forall hR_nonneg)]
    exact ENNReal.ofReal_lt_top
  have hY_bound : ∫⁻ ω, ENNReal.ofReal (Y ω) ∂μ ≤
      ∫⁻ ω, ENNReal.ofReal (R ω) ∂μ := by
    simpa only [setLIntegral_univ] using hsetL Set.univ MeasurableSet.univ
  have hY_norm : (fun ω ↦ ENNReal.ofReal ‖Y ω‖) =ᵐ[μ]
      fun ω ↦ ENNReal.ofReal (Y ω) := by
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hY_nonneg ω)]
  have hY_finite : ∫⁻ ω, ENNReal.ofReal ‖Y ω‖ ∂μ < ⊤ := by
    rw [lintegral_congr_ae hY_norm]
    exact hY_bound.trans_lt hR_finite
  have hY_int : Integrable Y μ :=
    ⟨hY_meas.aestronglyMeasurable, (hasFiniteIntegral_iff_norm Y).2 hY_finite⟩
  refine ⟨by simpa only [Y] using hY_int, ?_⟩
  apply (condExp_le_iff_forall_setIntegral_le (m := m) (μ := μ)
    hm hY_int hR_int hR_meas).2
  intro A hA
  have hlin := hsetL A hA
  have hYeq := ofReal_integral_eq_lintegral_ofReal (μ := μ.restrict A)
    hY_int.integrableOn (Filter.Eventually.of_forall hY_nonneg)
  have hReq := ofReal_integral_eq_lintegral_ofReal (μ := μ.restrict A)
    hR_int.integrableOn (Filter.Eventually.of_forall hR_nonneg)
  rw [← hYeq, ← hReq] at hlin
  have hRset_nonneg : 0 ≤ ∫ ω in A, R ω ∂μ :=
    setIntegral_nonneg_of_ae (Filter.Eventually.of_forall hR_nonneg)
  have hreal := (ENNReal.ofReal_le_ofReal_iff hRset_nonneg).mp hlin
  simpa only [Y, R] using hreal

/-! ### Second moment from the tail bound -/

/-- A nonnegative random variable with the indicated threshold-plus-exponential tail has a
finite Lebesgue second moment.  The conclusion is stated in `ℝ≥0∞` so finiteness is not assumed
in advance.
-/
theorem lintegral_second_moment_le_of_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX_meas : Measurable X)
    (hX_nonneg : ∀ ω, 0 ≤ X ω) {K c C d : ℝ} (hK : 0 ≤ K) (hc : 0 < c)
    (hC : 0 ≤ C) (hd : 0 < d)
    (hTail : ∀ r : ℝ, 0 < r →
      P.real {ω | r < X ω} ≤
        (if K > c * r then (1 : ℝ) else 0) + C * Real.exp (-d * r)) :
    ∫⁻ ω, ENNReal.ofReal (X ω ^ (2 : ℕ)) ∂P ≤
      ENNReal.ofReal ((K / c) ^ 2 + 2 * C / d ^ 2) := by
  have hlayer := lintegral_rpow_eq_lintegral_meas_lt_mul P
    (Filter.Eventually.of_forall hX_nonneg) hX_meas.aemeasurable
      (p := (2 : ℝ)) (by norm_num)
  have hlayer' :
      ∫⁻ ω, ENNReal.ofReal (X ω ^ (2 : ℕ)) ∂P =
        ENNReal.ofReal (2 : ℝ) *
          ∫⁻ r : ℝ in Ioi 0, P {ω | r < X ω} * ENNReal.ofReal r := by
    simpa [Real.rpow_natCast, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one] using hlayer
  have htailInt :
      ∫⁻ r : ℝ in Ioi 0, P {ω | r < X ω} * ENNReal.ofReal r ≤
        ∫⁻ r : ℝ in Ioi 0,
          ENNReal.ofReal (((if K > c * r then (1 : ℝ) else 0) + C * Real.exp (-d * r)) * r) := by
    apply setLIntegral_mono_ae
    · have hm : Measurable (fun r : ℝ =>
          ENNReal.ofReal (((if K > c * r then (1 : ℝ) else 0) + C * Real.exp (-d * r)) * r)) := by
        have hi : Measurable (fun r : ℝ => if K > c * r then (1 : ℝ) else 0) :=
          Measurable.ite (measurableSet_lt ((measurable_const (a := c)).mul measurable_id)
            (measurable_const (a := K))) measurable_const measurable_const
        have he : Measurable (fun r : ℝ => Real.exp (-d * r)) := by
          have hneg : Measurable (fun r : ℝ => -d * r) :=
            (measurable_const (a := -d)).mul measurable_id
          exact hneg.exp
        exact (hi.add ((measurable_const (a := C)).mul he)).mul measurable_id |>.ennreal_ofReal
      exact hm.aemeasurable
    · exact Filter.Eventually.of_forall (fun r hr => by
        have hrpos : 0 < r := mem_Ioi.mp hr
        have hq : 0 ≤ (if K > c * r then (1 : ℝ) else 0) + C * Real.exp (-d * r) := by
          positivity
        have hmeasure : P {ω | r < X ω} = ENNReal.ofReal (P.real {ω | r < X ω}) := by
          rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top P _)]
        rw [hmeasure]
        calc
          ENNReal.ofReal (P.real {ω | r < X ω}) * ENNReal.ofReal r ≤
              ENNReal.ofReal (((if K > c * r then (1 : ℝ) else 0) + C * Real.exp (-d * r))) *
                ENNReal.ofReal r := by
                exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (hTail r hrpos))
                  (by positivity)
          _ = ENNReal.ofReal (((if K > c * r then (1 : ℝ) else 0) + C * Real.exp (-d * r)) * r) := by
            exact (ENNReal.ofReal_mul hq).symm)
  calc
    ∫⁻ ω, ENNReal.ofReal (X ω ^ (2 : ℕ)) ∂P =
        ENNReal.ofReal (2 : ℝ) *
          ∫⁻ r : ℝ in Ioi 0, P {ω | r < X ω} * ENNReal.ofReal r := hlayer'
    _ ≤ ENNReal.ofReal (2 : ℝ) *
        ∫⁻ r : ℝ in Ioi 0,
          ENNReal.ofReal (((if K > c * r then (1 : ℝ) else 0) + C * Real.exp (-d * r)) * r) := by
        exact mul_le_mul_of_nonneg_left htailInt (by positivity)
    _ ≤ ENNReal.ofReal (2 : ℝ) * ENNReal.ofReal ((K / c) ^ 2 / 2 + C / d ^ 2) := by
        exact mul_le_mul_of_nonneg_left (lintegral_tail_weight_le hK hc hC hd) (by positivity)
    _ = ENNReal.ofReal ((K / c) ^ 2 + 2 * C / d ^ 2) := by
        rw [← ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ))]
        congr 1
        ring

/-- The same tail bound, with the finite second moment and its Bochner integral exposed. -/
theorem integrable_second_moment_le_of_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX_meas : Measurable X)
    (hX_nonneg : ∀ ω, 0 ≤ X ω) {K c C d : ℝ} (hK : 0 ≤ K) (hc : 0 < c)
    (hC : 0 ≤ C) (hd : 0 < d)
    (hTail : ∀ r : ℝ, 0 < r →
      P.real {ω | r < X ω} ≤
        (if K > c * r then (1 : ℝ) else 0) + C * Real.exp (-d * r)) :
    Integrable (fun ω => X ω ^ (2 : ℕ)) P ∧
      ∫ ω, X ω ^ (2 : ℕ) ∂P ≤ (K / c) ^ 2 + 2 * C / d ^ 2 := by
  let Y : Ω → ℝ := fun ω => X ω ^ (2 : ℕ)
  have hY_meas : Measurable Y := by
    exact hX_meas.pow measurable_const
  have hY_nonneg : ∀ ω, 0 ≤ Y ω := by
    intro ω
    exact sq_nonneg (X ω)
  have hbound : ∫⁻ ω, ENNReal.ofReal (Y ω) ∂P ≤
      ENNReal.ofReal ((K / c) ^ 2 + 2 * C / d ^ 2) := by
    simpa [Y] using
      lintegral_second_moment_le_of_tail P X hX_meas hX_nonneg hK hc hC hd hTail
  have hnorm : (fun ω => ENNReal.ofReal ‖Y ω‖) =ᵐ[P]
      (fun ω => ENNReal.ofReal (Y ω)) := by
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hY_nonneg ω)]
  have hfinite : ∫⁻ ω, ENNReal.ofReal ‖Y ω‖ ∂P < ⊤ := by
    rw [lintegral_congr_ae hnorm]
    exact hbound.trans_lt (ENNReal.ofReal_lt_top)
  have hY_int : Integrable Y P :=
    ⟨hY_meas.aestronglyMeasurable, (hasFiniteIntegral_iff_norm Y).2 hfinite⟩
  refine ⟨?_, ?_⟩
  · simpa [Y] using hY_int
  have hEq := ofReal_integral_eq_lintegral_ofReal hY_int
    (Filter.Eventually.of_forall hY_nonneg)
  have hreal : ENNReal.ofReal (∫ ω, Y ω ∂P) ≤
      ENNReal.ofReal ((K / c) ^ 2 + 2 * C / d ^ 2) := by
    rw [hEq]
    exact hbound
  have hB : 0 ≤ (K / c) ^ 2 + 2 * C / d ^ 2 := by positivity
  have hreal' := (ENNReal.ofReal_le_ofReal_iff hB).mp hreal
  simpa [Y] using hreal'

/-! ### Finite-family Fubini -/

/-- Finite-index sum/Fubini form of the second-moment estimate. -/
theorem finset_lintegral_second_moment_le_of_tail {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (s : Finset ι) (X : ι → Ω → ℝ)
    (K c C d : ι → ℝ) (hX_meas : ∀ i ∈ s, Measurable (X i))
    (hX_nonneg : ∀ i ∈ s, ∀ ω, 0 ≤ X i ω)
    (hK : ∀ i ∈ s, 0 ≤ K i) (hc : ∀ i ∈ s, 0 < c i)
    (hC : ∀ i ∈ s, 0 ≤ C i) (hd : ∀ i ∈ s, 0 < d i)
    (hTail : ∀ i ∈ s, ∀ r : ℝ, 0 < r →
      P.real {ω | r < X i ω} ≤
        (if K i > c i * r then (1 : ℝ) else 0) + C i * Real.exp (-d i * r)) :
    ∫⁻ ω, (∑ i ∈ s, ENNReal.ofReal (X i ω ^ (2 : ℕ))) ∂P ≤
      ∑ i ∈ s, ENNReal.ofReal ((K i / c i) ^ 2 + 2 * C i / d i ^ 2) := by
  have hfubini :
      ∫⁻ ω, (∑ i ∈ s, ENNReal.ofReal (X i ω ^ (2 : ℕ))) ∂P =
        ∑ i ∈ s, ∫⁻ ω, ENNReal.ofReal (X i ω ^ (2 : ℕ)) ∂P := by
    apply lintegral_finsetSum
    intro i hi
    exact ((hX_meas i hi).pow measurable_const).ennreal_ofReal
  rw [hfubini]
  apply Finset.sum_le_sum
  intro i hi
  exact lintegral_second_moment_le_of_tail P (X i) (hX_meas i hi) (hX_nonneg i hi)
    (hK i hi) (hc i hi) (hC i hi) (hd i hi) (hTail i hi)

end OTSelector
