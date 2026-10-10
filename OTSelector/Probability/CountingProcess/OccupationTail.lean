import OTSelector.Probability.CountingProcess.OccupationBound
import OTSelector.Probability.CountingProcess.RightGridStopping
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Conditional lower occupation for counting processes

This module turns the finite-horizon negative-tilt martingale into the conditional lower-tail
estimate used by the lower-occupation lemmas in `main.tex`.  The survival event remains inside the
conditional probability.  The first theorem treats a finite stopping grid; a later section
removes the grid restriction by right-grid approximation.
-/

open Filter Set
open scoped ENNReal NNReal MeasureTheory ProbabilityTheory Topology

namespace OTSelector.CountingProcess

open _root_.MeasureTheory

variable {Ω : Type*} [hΩ : MeasurableSpace Ω]

/-- Exponential decay rate produced by the negative counting tilt. -/
noncomputable def lowerOccupationExponent (θ c₀ a : ℝ) : ℝ :=
  (1 - Real.exp (-θ)) * c₀ - θ * a

omit [MeasurableSpace Ω] in
theorem lowerOccupationExponent_rescaled_mul {theta c₀ a r r' : ℝ} (hr' : r' ≠ 0) :
    lowerOccupationExponent theta c₀ (a * r / r') * r' =
      (1 - Real.exp (-theta)) * c₀ * r' - theta * a * r := by
  rw [lowerOccupationExponent]
  field_simp

/-- A pathwise lower intensity bound integrates to the corresponding lower bound for the
compensator increment. -/
theorem integratedIntensity_one_sub_lower {μ : Measure Ω}
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {N : ℝ≥0 → Ω → ℕ}
    {Λ : ℝ≥0 → Ω → ℝ} (hΛ : HasPredictableIntensity μ ℱ N Λ)
    {s t : ℝ≥0} (hst : s ≤ t) {ω : Ω} {c₀ : ℝ}
    (hΛlower : ∀ u ∈ Ioc s t, c₀ ≤ Λ u ω) :
    c₀ * ((t : ℝ) - (s : ℝ)) ≤
      integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) t ω -
        integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) s ω := by
  have hHI : IntervalIntegrable (fun x : ℝ ↦ Λ (Real.toNNReal x) ω)
      volume 0 (t : ℝ) :=
    intervalIntegrable_toReal_of_integrableOn (hΛ.integrableOn t ω)
  have hadd := integratedIntensity_add_Ioc (H := fun _ _ ↦ (1 : ℝ))
    (w := 0) (v := s) (u := t) (by simp) hst (by simpa using hHI)
  have hA0 : integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) 0 ω = 0 := by
    simp [integratedIntensity]
  have hAs : integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) s ω =
      ∫ u in Ioc (0 : ℝ≥0) s, Λ u ω ∂timeMeasure := by
    simp [integratedIntensity]
  have hdiff : integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) t ω -
      integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) s ω =
        ∫ u in Ioc s t, Λ u ω ∂timeMeasure := by
    rw [hA0] at hadd
    simp only [zero_add, one_mul] at hadd
    rw [← hAs] at hadd
    linarith
  have hconstInt : IntegrableOn (fun _ : ℝ≥0 ↦ c₀) (Ioc s t) timeMeasure :=
    integrableOn_const (C := c₀) (timeMeasure_Ioc_lt_top s t).ne
  have hLamInt : IntegrableOn (fun u ↦ Λ u ω) (Ioc s t) timeMeasure := by
    exact (hΛ.integrableOn t ω).mono_set fun u hu ↦
      ⟨lt_of_le_of_lt s.2 hu.1, hu.2⟩
  have hmono : (∫ u in Ioc s t, c₀ ∂timeMeasure) ≤
      ∫ u in Ioc s t, Λ u ω ∂timeMeasure :=
    setIntegral_mono_on hconstInt hLamInt measurableSet_Ioc hΛlower
  have hconst : (∫ _u in Ioc s t, c₀ ∂timeMeasure) =
      c₀ * ((t : ℝ) - (s : ℝ)) := by
    rw [integral_timeMeasure_eq_intervalIntegral (fun _ : ℝ≥0 ↦ c₀) s t
      (by exact_mod_cast hst)]
    rw [intervalIntegral.integral_const]
    ring
  rw [hdiff, ← hconst]
  exact hmono

omit [MeasurableSpace Ω] in
/-- Additive-exponent form of the constant negative-tilt counting exponential. -/
theorem countingExponential_const_neg_eq_exp (N : ℝ≥0 → Ω → ℕ)
    (Λ : ℝ≥0 → Ω → ℝ) (θ : ℝ) (t : ℝ≥0) (ω : Ω)
    (hΛint : IntegrableOn (fun s ↦ Λ s ω) (Ioc (0 : ℝ≥0) t) timeMeasure) :
    countingExponential N Λ (fun _ _ ↦ -θ) t ω =
      Real.exp (-θ * (N t ω : ℝ) +
        (1 - Real.exp (-θ)) * integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) t ω) := by
  rw [countingExponential_pow_exp N Λ θ t ω hΛint, ← Real.exp_nat_mul,
    ← Real.exp_add]
  congr 1
  ring

/-- On an interval with enough accumulated intensity, a small count increment forces the
negative-tilt exponential to grow by the displayed deterministic factor. -/
theorem countingExponential_interval_lower {μ : Measure Ω}
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {N : ℝ≥0 → Ω → ℕ}
    {Λ : ℝ≥0 → Ω → ℝ} (hΛ : HasPredictableIntensity μ ℱ N Λ)
    {θ c₀ a : ℝ} (hθ : 0 < θ) {s t : ℝ≥0} {ω : Ω}
    (hcount : (N t ω : ℝ) - N s ω ≤ a * ((t : ℝ) - (s : ℝ)))
    (hA : c₀ * ((t : ℝ) - (s : ℝ)) ≤
      integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) t ω -
        integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) s ω) :
    Real.exp (lowerOccupationExponent θ c₀ a * ((t : ℝ) - (s : ℝ))) *
        countingExponential N Λ (fun _ _ ↦ -θ) s ω ≤
      countingExponential N Λ (fun _ _ ↦ -θ) t ω := by
  have hc : 0 ≤ 1 - Real.exp (-θ) := by
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  rw [countingExponential_const_neg_eq_exp N Λ θ s ω (hΛ.integrableOn s ω),
    countingExponential_const_neg_eq_exp N Λ θ t ω (hΛ.integrableOn t ω),
    ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  dsimp [lowerOccupationExponent]
  nlinarith

/-- The negative-tilt exponential is uniformly bounded above on a finite horizon when the
intensity has a deterministic upper bound. -/
theorem countingExponential_const_neg_le {μ : Measure Ω}
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {N : ℝ≥0 → Ω → ℕ}
    {Λ : ℝ≥0 → Ω → ℝ} (hΛ : HasPredictableIntensity μ ℱ N Λ)
    {θ C₀ : ℝ} (hθ : 0 < θ) (hC₀ : 0 ≤ C₀)
    (hΛupper : ∀ u ω, Λ u ω ≤ C₀) {t T : ℝ≥0} (htT : t ≤ T) (ω : Ω) :
    countingExponential N Λ (fun _ _ ↦ -θ) t ω ≤
      Real.exp ((1 - Real.exp (-θ)) * C₀ * (T : ℝ)) := by
  have hc : 0 ≤ 1 - Real.exp (-θ) := by
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  have hA := integratedIntensity_one_nonneg_le (hC₀ := hC₀) hΛ hΛupper t ω
  rw [countingExponential_const_neg_eq_exp N Λ θ t ω (hΛ.integrableOn t ω)]
  apply Real.exp_le_exp.mpr
  have hNt : 0 ≤ (N t ω : ℝ) := by positivity
  have ht : (t : ℝ) ≤ (T : ℝ) := by exact_mod_cast htT
  have hneg : -θ * (N t ω : ℝ) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hNt
  have hca : (1 - Real.exp (-θ)) *
      integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) t ω ≤
        (1 - Real.exp (-θ)) * (C₀ * (t : ℝ)) :=
    mul_le_mul_of_nonneg_left hA.2 hc
  have hCt : C₀ * (t : ℝ) ≤ C₀ * (T : ℝ) :=
    mul_le_mul_of_nonneg_left ht hC₀
  have hcCt := mul_le_mul_of_nonneg_left hCt hc
  nlinarith

/-! ## Conditional exponential Markov inequality -/

/-- A conditional Markov inequality in the multiplicative form used below.  The random
normalizer `X` is allowed to be nonconstant because it is the conditional expectation of `Y`.
This avoids dividing by the counting exponential at the starting stopping coordinate. -/
theorem condExp_indicator_le_inv_of_scaled
    {m : MeasurableSpace Ω} {μ : @Measure Ω hΩ} [IsFiniteMeasure μ]
    {E : Set Ω} (hE : @MeasurableSet Ω hΩ E) {X Y : Ω → ℝ} {R : ℝ}
    (hR : 0 < R) (hXpos : ∀ ω, 0 < X ω) (hYnonneg : ∀ ω, 0 ≤ Y ω)
    (hscaled : ∀ ω ∈ E, R * X ω ≤ Y ω) (hYint : Integrable Y μ)
    (hCE : μ[Y | m] =ᵐ[μ] X) :
    μ[E.indicator (fun _ ↦ (1 : ℝ)) | m] ≤ᵐ[μ] fun _ ↦ R⁻¹ := by
  let I : Ω → ℝ := E.indicator fun _ ↦ (1 : ℝ)
  have hXint : Integrable X μ := integrable_condExp.congr hCE
  have hIint : Integrable I μ := by
    apply Integrable.mono' (integrable_const (1 : ℝ))
    · exact stronglyMeasurable_const.indicator hE |>.aestronglyMeasurable
    · filter_upwards with ω
      simp only [I]
      by_cases hω : ω ∈ E <;> simp [hω]
  have hXIint : Integrable (fun ω ↦ (R * X ω) * I ω) μ := by
    have hRX : Integrable (fun ω ↦ R * X ω) μ := hXint.const_mul R
    have heq : (fun ω ↦ (R * X ω) * I ω) =
        E.indicator (fun ω ↦ R * X ω) := by
      funext ω
      by_cases hω : ω ∈ E <;> simp [I, hω]
    rw [heq]
    exact hRX.indicator hE
  have hpoint : (fun ω ↦ (R * X ω) * I ω) ≤ fun ω ↦ Y ω := by
    intro ω
    by_cases hω : ω ∈ E
    · simpa [I, hω] using hscaled ω hω
    · simpa [I, hω] using hYnonneg ω
  have hmono : μ[fun ω ↦ (R * X ω) * I ω | m] ≤ᵐ[μ] μ[Y | m] :=
    condExp_mono hXIint hYint (Eventually.of_forall hpoint)
  have hXm : AEStronglyMeasurable[m] X μ :=
    stronglyMeasurable_condExp.aestronglyMeasurable.congr hCE
  have hpull : μ[fun ω ↦ (R * X ω) * I ω | m] =ᵐ[μ]
      fun ω ↦ (R * X ω) * μ[I | m] ω := by
    change μ[(fun ω ↦ R * X ω) * I | m] =ᵐ[μ]
      (fun ω ↦ R * X ω) * μ[I | m]
    exact condExp_mul_of_aestronglyMeasurable_left (hXm.const_mul R) hXIint hIint
  filter_upwards [hmono, hpull, hCE] with ω hmonoω hpullω hCEω
  rw [hpullω, hCEω] at hmonoω
  have hcancel : R * μ[I | m] ω ≤ 1 := by
    have hXω := hXpos ω
    nlinarith
  have hout : μ[I | m] ω ≤ R⁻¹ := by
    rw [inv_eq_one_div]
    exact (le_div_iff₀ hR).2 (by simpa [mul_comm] using hcancel)
  simpa [I] using hout

/-- If `m₁ ≤ m₂`, an indicator bound conditioned on `m₂` descends to `m₁`.
The smaller event may be replaced by any measurable subset before applying the tower property. -/
theorem condExp_indicator_le_of_subset_of_larger
    {m₁ m₂ : MeasurableSpace Ω} {mu : @Measure Ω hΩ} [IsFiniteMeasure mu]
    (hm₁₂ : m₁ ≤ m₂) (hm₂ : m₂ ≤ hΩ) {E F : Set Ω}
    (hE : @MeasurableSet Ω hΩ E) (hF : @MeasurableSet Ω hΩ F)
    (hEF : E ⊆ F) {c : ℝ}
    (hbound : mu[F.indicator (fun _ ↦ (1 : ℝ)) | m₂] ≤ᵐ[mu] fun _ ↦ c) :
    mu[E.indicator (fun _ ↦ (1 : ℝ)) | m₁] ≤ᵐ[mu] fun _ ↦ c := by
  let IE : Ω → ℝ := E.indicator fun _ ↦ 1
  let IF : Ω → ℝ := F.indicator fun _ ↦ 1
  have hIEint : Integrable IE mu :=
    (integrable_const (1 : ℝ)).indicator hE
  have hIFint : Integrable IF mu :=
    (integrable_const (1 : ℝ)).indicator hF
  have hIEIF : IE ≤ IF := by
    intro ω
    by_cases hωE : ω ∈ E
    · have hωF : ω ∈ F := hEF hωE
      simp [IE, IF, hωE, hωF]
    · by_cases hωF : ω ∈ F <;> simp [IE, IF, hωE, hωF]
  have hmono₁ : mu[IE | m₁] ≤ᵐ[mu] mu[IF | m₁] :=
    condExp_mono hIEint hIFint (Eventually.of_forall hIEIF)
  have htower : mu[mu[IF | m₂] | m₁] =ᵐ[mu] mu[IF | m₁] :=
    condExp_condExp_of_le hm₁₂ hm₂
  have hcondBound : mu[mu[IF | m₂] | m₁] ≤ᵐ[mu]
      mu[fun _ : Ω ↦ c | m₁] :=
    condExp_mono integrable_condExp (integrable_const c) hbound
  have hconst : mu[fun _ : Ω ↦ c | m₁] = fun _ ↦ c :=
    condExp_const (hm₁₂.trans hm₂) c
  filter_upwards [hmono₁, htower, hcondBound] with ω hmonoω htowerω hboundω
  change mu[IE | m₁] ω ≤ c
  rw [htowerω] at hboundω
  rw [hconst] at hboundω
  exact hmonoω.trans hboundω

/-- Integrating an almost-everywhere conditional indicator bound gives the corresponding
unconditional probability bound. -/
theorem measureReal_le_of_condExp_indicator_le_const
    {m : MeasurableSpace Ω} {mu : @Measure Ω hΩ} [IsProbabilityMeasure mu]
    (hm : m ≤ hΩ) {E : Set Ω} (hE : @MeasurableSet Ω hΩ E) {c : ℝ}
    (hbound : mu[E.indicator (fun _ ↦ (1 : ℝ)) | m] ≤ᵐ[mu] fun _ ↦ c) :
    mu.real E ≤ c := by
  have hmono :
      ∫ omega, mu[E.indicator (fun _ ↦ (1 : ℝ)) | m] omega ∂mu ≤
        ∫ _omega, c ∂mu :=
    integral_mono_ae integrable_condExp (integrable_const c) hbound
  have hindicator : (∫ omega, E.indicator (fun _ ↦ (1 : ℝ)) omega ∂mu) =
      mu.real E := by
    change (∫ omega, E.indicator (1 : Ω → ℝ) omega ∂mu) = mu.real E
    exact integral_indicator_one (μ := mu) hE
  rw [integral_condExp hm, hindicator, integral_const] at hmono
  simpa using hmono

omit [MeasurableSpace Ω] in
/-- A lower-count event starting at `σ` is contained in the event starting at the next grid
point, provided the duration is shortened by one mesh.  The count threshold is rescaled so its
total value remains exactly `a * r`. -/
theorem stoppedLowerOccupationEvent_subset_rightGrid
    {N : ℝ≥0 → Ω → ℕ} {sigma : Ω → ℝ≥0} {tau : Ω → WithTop ℝ≥0}
    {a : ℝ} {r : ℝ≥0} (hNmono : ∀ omega, Monotone fun t ↦ N t omega)
    (n : ℕ) (hn : 0 < n) (hmesh : (n : ℝ≥0)⁻¹ < r) :
    stoppedLowerOccupationEvent N sigma tau a r ⊆
      stoppedLowerOccupationEvent N (fun omega ↦ rightGrid n (sigma omega)) tau
        (a * (r : ℝ) / ((r - (n : ℝ≥0)⁻¹ : ℝ≥0) : ℝ))
        (r - (n : ℝ≥0)⁻¹) := by
  intro omega hω
  let delta : ℝ≥0 := (n : ℝ≥0)⁻¹
  let sigman : ℝ≥0 := rightGrid n (sigma omega)
  let rn : ℝ≥0 := r - delta
  have hsigma_le : sigma omega ≤ sigman := le_rightGrid n (sigma omega) hn
  have hsigman_lt : sigman < sigma omega + delta :=
    rightGrid_lt_add_inv n (sigma omega) hn
  have hdelta_le : delta ≤ r := hmesh.le
  have hend : sigman + rn ≤ sigma omega + r := by
    calc
      sigman + rn ≤ (sigma omega + delta) + rn :=
        add_le_add_left hsigman_lt.le rn
      _ = sigma omega + (delta + rn) := by ac_rfl
      _ = sigma omega + r := by rw [add_tsub_cancel_of_le hdelta_le]
  have hstartCount : (N (sigma omega) omega : ℝ) ≤ N sigman omega := by
    exact_mod_cast hNmono omega hsigma_le
  have hendCount : (N (sigman + rn) omega : ℝ) ≤ N (sigma omega + r) omega := by
    exact_mod_cast hNmono omega hend
  have hrn_pos : 0 < (rn : ℝ) := by
    exact_mod_cast tsub_pos_iff_lt.mpr hmesh
  have hthreshold :
      (a * (r : ℝ) / (rn : ℝ)) * (rn : ℝ) = a * (r : ℝ) :=
    div_mul_cancel₀ _ hrn_pos.ne'
  constructor
  · change (N (sigman + rn) omega : ℝ) - N sigman omega ≤
      (a * (r : ℝ) / (rn : ℝ)) * (rn : ℝ)
    rw [hthreshold]
    linarith [hω.1]
  · exact (WithTop.coe_le_coe.mpr hend).trans hω.2

/-! ## Finite stopping grids -/

/-- Conditional lower occupation on a finite stopping grid.  The event keeps the future survival
condition `σ+r ≤ τ` inside the conditional expectation.  No measurability or predictability of the
arbitrary endpoint `τ` beyond the stopping-time property is used. -/
theorem condExp_stoppedLowerOccupationEvent_le_finiteRange
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {N : ℝ≥0 → Ω → ℕ}
    {Λ : ℝ≥0 → Ω → ℝ} {σ : Ω → ℝ≥0} {τ : Ω → WithTop ℝ≥0}
    {θ c₀ C₀ a : ℝ} {B r : ℝ≥0}
    (hθ : 0 < θ) (hC₀ : 0 ≤ C₀) (hN : IsSimpleCountingProcess ℱ N)
    (hΛ : HasPredictableIntensity μ ℱ N Λ) (hΛupper : ∀ u ω, Λ u ω ≤ C₀)
    (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : WithTop ℝ≥0))
    (hσ_range : (Set.range σ).Finite) (hσB : ∀ ω, σ ω ≤ B)
    (hτ : IsStoppingTime ℱ τ)
    (hΛlower : ∀ (u : ℝ≥0) ω, (u : WithTop ℝ≥0) ≤ τ ω → c₀ ≤ Λ u ω) :
    μ[(stoppedLowerOccupationEvent N σ τ a r).indicator (fun _ ↦ (1 : ℝ)) |
        hσ.measurableSpace] ≤ᵐ[μ]
      fun _ ↦ Real.exp (-lowerOccupationExponent θ c₀ a * (r : ℝ)) := by
  let T : ℝ≥0 := B + r
  let Z : ℝ≥0 → Ω → ℝ :=
    finiteHorizonCountingExponential N Λ θ T
  let ρ : Ω → ℝ≥0 := fun ω ↦ σ ω + r
  let X : Ω → ℝ := fun ω ↦ Z (σ ω) ω
  let Y : Ω → ℝ := fun ω ↦ Z (ρ ω) ω
  let R : ℝ := Real.exp (lowerOccupationExponent θ c₀ a * (r : ℝ))
  have hM : Martingale Z ℱ μ :=
    finiteHorizonCountingExponential_martingale
      hθ hC₀ hΛupper hN hΛ
  have hρ := IsStoppingTime.coe_add_const_finiteRange hσ hσ_range r
  have hσT : ∀ ω, (σ ω : WithTop ℝ≥0) ≤ T := by
    intro ω
    exact_mod_cast (hσB ω).trans (le_add_right (le_refl B))
  have hρT : ∀ ω, (ρ ω : WithTop ℝ≥0) ≤ T := by
    intro ω
    change ((σ ω + r : ℝ≥0) : WithTop ℝ≥0) ≤ (B + r : ℝ≥0)
    exact_mod_cast (by simpa [add_comm] using add_le_add_right (hσB ω) r)
  have hσρ : ∀ ω, (σ ω : WithTop ℝ≥0) ≤ ρ ω := by
    intro ω
    exact_mod_cast le_add_right (le_refl (σ ω))
  have hσcoe_range : (Set.range fun ω ↦ (σ ω : WithTop ℝ≥0)).Finite := by
    rw [show (fun ω ↦ (σ ω : WithTop ℝ≥0)) =
      (fun s : ℝ≥0 ↦ (s : WithTop ℝ≥0)) ∘ σ by rfl, Set.range_comp]
    exact hσ_range.image fun s : ℝ≥0 ↦ (s : WithTop ℝ≥0)
  have hρ_range : (Set.range ρ).Finite := by
    rw [show ρ = (fun s : ℝ≥0 ↦ s + r) ∘ σ by rfl, Set.range_comp]
    exact hσ_range.image fun s : ℝ≥0 ↦ s + r
  have hCEraw := hM.stoppedValue_ae_eq_condExp_of_le_of_countable_range
    hρ.1 hσ hσρ hρT hρ.2.countable hσcoe_range.countable
  have hstopσ : stoppedValue Z (fun ω ↦ (σ ω : WithTop ℝ≥0)) = X := by
    funext ω
    unfold stoppedValue
    rw [WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
  have hstopρ : stoppedValue Z
      (fun ω ↦ ((σ ω + r : ℝ≥0) : WithTop ℝ≥0)) = Y := by
    funext ω
    unfold stoppedValue
    rw [WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
  have hCE : μ[Y | hσ.measurableSpace] =ᵐ[μ] X := by
    rw [hstopσ, hstopρ] at hCEraw
    exact hCEraw.symm
  have hE := measurableSet_stoppedLowerOccupationEvent_finiteRange
    (a := a) (r := r) hN hσ hσ_range hτ
  have hYmeas : StronglyMeasurable Y := by
    apply stronglyMeasurable_eval_finiteRange (hM.stronglyAdapted) hρ.1 hρ_range
  have hYint : Integrable Y μ := by
    apply Integrable.mono' (integrable_const
      (Real.exp ((1 - Real.exp (-θ)) * C₀ * (T : ℝ))))
    · exact hYmeas.aestronglyMeasurable
    · filter_upwards with ω
      have hnonneg : 0 ≤ Y ω := by
        exact (countingExponential_pos N Λ (fun _ _ ↦ -θ) (min (ρ ω) T) ω).le
      have hupper : Y ω ≤
          Real.exp ((1 - Real.exp (-θ)) * C₀ * (T : ℝ)) := by
        dsimp [Y, Z, finiteHorizonCountingExponential]
        exact countingExponential_const_neg_le hΛ hθ hC₀ hΛupper
          (min_le_right (ρ ω) T) ω
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg,
        abs_of_pos (Real.exp_pos _)] using hupper
  have hscaled : ∀ ω ∈ stoppedLowerOccupationEvent N σ τ a r,
      R * X ω ≤ Y ω := by
    intro ω hω
    have hst : σ ω ≤ ρ ω := le_add_right (le_refl (σ ω))
    have hlower : ∀ u ∈ Ioc (σ ω) (ρ ω), c₀ ≤ Λ u ω := by
      intro u hu
      apply hΛlower u ω
      exact (WithTop.coe_le_coe.mpr hu.2).trans hω.2
    have hA := integratedIntensity_one_sub_lower hΛ hst hlower
    have hcount : (N (ρ ω) ω : ℝ) - N (σ ω) ω ≤
        a * ((ρ ω : ℝ) - (σ ω : ℝ)) := by
      simpa [ρ] using hω.1
    have hpath := countingExponential_interval_lower hΛ hθ hcount hA
    simpa [R, X, Y, Z, finiteHorizonCountingExponential, ρ,
      min_eq_left (show σ ω ≤ T by exact_mod_cast hσT ω),
      min_eq_left (show ρ ω ≤ T by exact_mod_cast hρT ω)] using hpath
  have hXpos : ∀ ω, 0 < X ω := by
    intro ω
    exact countingExponential_pos N Λ (fun _ _ ↦ -θ) (min (σ ω) T) ω
  have hYnonneg : ∀ ω, 0 ≤ Y ω := fun ω ↦
    (countingExponential_pos N Λ (fun _ _ ↦ -θ) (min (ρ ω) T) ω).le
  have hmarkov := condExp_indicator_le_inv_of_scaled hE (Real.exp_pos _)
    hXpos hYnonneg hscaled hYint hCE
  filter_upwards [hmarkov] with ω hω
  rw [show -lowerOccupationExponent θ c₀ a * (r : ℝ) =
    -(lowerOccupationExponent θ c₀ a * (r : ℝ)) by ring, Real.exp_neg]
  exact hω

/-! ## Arbitrary bounded stopping coordinates -/

/-- Conditional lower occupation from an arbitrary deterministically bounded stopping
coordinate.  Right-grid starts have finite range.  The original event is included in a grid
event with one mesh removed from the duration; the tower property then brings the estimate back
to the sigma-algebra at the original stopping coordinate. -/
theorem condExp_stoppedLowerOccupationEvent_le_boundedStopping
    {mu : Measure Ω} [IsFiniteMeasure mu]
    {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {N : ℝ≥0 → Ω → ℕ}
    {Lambda : ℝ≥0 → Ω → ℝ} {sigma : Ω → ℝ≥0} {tau : Ω → WithTop ℝ≥0}
    {theta c₀ C₀ a : ℝ} {B r : ℝ≥0}
    (htheta : 0 < theta) (hC₀ : 0 ≤ C₀) (hr : 0 < r)
    (hN : IsSimpleCountingProcess F N)
    (hLambda : HasPredictableIntensity mu F N Lambda)
    (hLambdaUpper : ∀ u omega, Lambda u omega ≤ C₀)
    (hsigma : IsStoppingTime F fun omega ↦ (sigma omega : WithTop ℝ≥0))
    (hsigmaB : ∀ omega, sigma omega ≤ B) (htau : IsStoppingTime F tau)
    (hLambdaLower : ∀ (u : ℝ≥0) omega, (u : WithTop ℝ≥0) ≤ tau omega → c₀ ≤ Lambda u omega) :
    mu[(stoppedLowerOccupationEvent N sigma tau a r).indicator (fun _ ↦ (1 : ℝ)) |
        hsigma.measurableSpace] ≤ᵐ[mu]
      fun _ ↦ Real.exp (-lowerOccupationExponent theta c₀ a * (r : ℝ)) := by
  let mesh : ℕ → ℝ≥0 := fun k ↦ (((k + 1 : ℕ) : ℝ≥0))⁻¹
  let short : ℕ → ℝ≥0 := fun k ↦ r - mesh k
  let bound : ℕ → ℝ := fun k ↦
    Real.exp (-((1 - Real.exp (-theta)) * c₀ * (short k : ℝ) -
      theta * a * (r : ℝ)))
  have hmeshTendsto : Tendsto mesh atTop (nhds 0) := by
    exact (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ≥0)).comp (tendsto_add_atTop_nat 1)
  have hshortTendstoNNReal : Tendsto short atTop (nhds r) := by
    simpa [short] using tendsto_const_nhds.sub hmeshTendsto
  have hshortTendsto : Tendsto (fun k ↦ (short k : ℝ)) atTop (nhds (r : ℝ)) :=
    (NNReal.continuous_coe.tendsto r).comp hshortTendstoNNReal
  have hboundTendsto : Tendsto bound atTop
      (nhds (Real.exp (-lowerOccupationExponent theta c₀ a * (r : ℝ)))) := by
    have hlinear : Tendsto
        (fun k ↦ -((1 - Real.exp (-theta)) * c₀ * (short k : ℝ) -
          theta * a * (r : ℝ))) atTop
        (nhds (-lowerOccupationExponent theta c₀ a * (r : ℝ))) := by
      convert (((tendsto_const_nhds.mul hshortTendsto).sub
        tendsto_const_nhds).neg) using 1; simp [lowerOccupationExponent]; ring
    exact Real.continuous_exp.continuousAt.tendsto.comp hlinear
  have hE : MeasurableSet (stoppedLowerOccupationEvent N sigma tau a r) :=
    measurableSet_stoppedLowerOccupationEvent_bounded hN hsigma hsigmaB htau
  have honeGrid : ∀ k, mesh k < r →
      mu[(stoppedLowerOccupationEvent N sigma tau a r).indicator (fun _ ↦ (1 : ℝ)) |
          hsigma.measurableSpace] ≤ᵐ[mu] fun _ ↦ bound k := by
    intro k hmesh
    let sigmak : Ω → ℝ≥0 := fun omega ↦ rightGrid (k + 1) (sigma omega)
    let ratek : ℝ := a * (r : ℝ) / (short k : ℝ)
    have hsigmak : IsStoppingTime F fun omega ↦ (sigmak omega : WithTop ℝ≥0) := by
      exact IsStoppingTime.rightGridApprox hsigma (k + 1) (by omega)
    have hsigmakRange : (Set.range sigmak).Finite := by
      exact finiteRange_rightGrid_of_le (k + 1) (by omega) hsigmaB
    have hsigmakB : ∀ omega, sigmak omega ≤ B + mesh k := by
      intro omega
      exact (rightGrid_lt_add_inv (k + 1) (sigma omega) (by omega)).le.trans
        (add_le_add_left (hsigmaB omega) (mesh k))
    have hgrid := condExp_stoppedLowerOccupationEvent_le_finiteRange
      (θ := theta) (c₀ := c₀) (C₀ := C₀) (a := ratek)
      (B := B + mesh k) (r := short k) htheta hC₀ hN hLambda hLambdaUpper
      hsigmak hsigmakRange hsigmakB htau hLambdaLower
    have hshortPos : 0 < (short k : ℝ) := by
      exact_mod_cast tsub_pos_iff_lt.mpr hmesh
    have hboundEq :
        Real.exp (-lowerOccupationExponent theta c₀ ratek * (short k : ℝ)) =
          bound k := by
      congr 1
      rw [show -lowerOccupationExponent theta c₀ ratek * (short k : ℝ) =
        -(lowerOccupationExponent theta c₀ ratek * (short k : ℝ)) by ring]
      rw [lowerOccupationExponent_rescaled_mul hshortPos.ne']
    rw [hboundEq] at hgrid
    have hFset : MeasurableSet
        (stoppedLowerOccupationEvent N sigmak tau ratek (short k)) :=
      measurableSet_stoppedLowerOccupationEvent_finiteRange hN hsigmak hsigmakRange htau
    have hsubset : stoppedLowerOccupationEvent N sigma tau a r ⊆
        stoppedLowerOccupationEvent N sigmak tau ratek (short k) := by
      simpa [sigmak, ratek, mesh, short] using
        stoppedLowerOccupationEvent_subset_rightGrid hN.monotone (k + 1) (by omega) hmesh
    have hm : hsigma.measurableSpace ≤ hsigmak.measurableSpace := by
      apply hsigma.measurableSpace_mono hsigmak
      intro omega
      simp only [sigmak, WithTop.coe_le_coe]
      exact le_rightGrid (k + 1) (sigma omega) (by omega)
    exact condExp_indicator_le_of_subset_of_larger hm hsigmak.measurableSpace_le
      hE hFset hsubset hgrid
  have hAll : ∀ᵐ omega ∂mu, ∀ k, mesh k < r →
      mu[(stoppedLowerOccupationEvent N sigma tau a r).indicator (fun _ ↦ (1 : ℝ)) |
          hsigma.measurableSpace] omega ≤ bound k := by
    rw [ae_all_iff]
    intro k
    by_cases hk : mesh k < r
    · exact (honeGrid k hk).mono fun omega hω _ ↦ hω
    · exact Eventually.of_forall fun _ hk' ↦ (hk hk').elim
  filter_upwards [hAll] with omega hω
  apply ge_of_tendsto hboundTendsto
  filter_upwards [(tendsto_order.1 hmeshTendsto).2 r hr] with k hk
  exact hω k hk

/-- The explicit count threshold used by the lower-occupation estimate in `main.tex`. -/
noncomputable def lowerOccupationCountRate (c₀ : ℝ) : ℝ :=
  c₀ * (1 - Real.exp (-1)) / 2

/-- The explicit exponential rate used by the lower-occupation estimate in `main.tex`. -/
noncomputable def lowerOccupationDecayRate (c₀ : ℝ) : ℝ :=
  c₀ * (1 - Real.exp (-1)) / 2

theorem lowerOccupation_rates_pos {c₀ : ℝ} (hc₀ : 0 < c₀) :
    0 < lowerOccupationCountRate c₀ ∧ 0 < lowerOccupationDecayRate c₀ := by
  have he : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  constructor <;> simp only [lowerOccupationCountRate, lowerOccupationDecayRate] <;> positivity

/-- Explicit finite-grid form of the stopped occupation estimate `(1.39b)`. -/
theorem condExp_stoppedLowerOccupationEvent_le_explicit
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {N : ℝ≥0 → Ω → ℕ}
    {Λ : ℝ≥0 → Ω → ℝ} {σ : Ω → ℝ≥0} {τ : Ω → WithTop ℝ≥0}
    {c₀ C₀ : ℝ} {B r : ℝ≥0}
    (_hc₀ : 0 < c₀) (hC₀ : 0 ≤ C₀) (hN : IsSimpleCountingProcess ℱ N)
    (hΛ : HasPredictableIntensity μ ℱ N Λ) (hΛupper : ∀ u ω, Λ u ω ≤ C₀)
    (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : WithTop ℝ≥0))
    (hσ_range : (Set.range σ).Finite) (hσB : ∀ ω, σ ω ≤ B)
    (hτ : IsStoppingTime ℱ τ)
    (hΛlower : ∀ (u : ℝ≥0) ω, (u : WithTop ℝ≥0) ≤ τ ω → c₀ ≤ Λ u ω) :
    μ[(stoppedLowerOccupationEvent N σ τ (lowerOccupationCountRate c₀) r).indicator
          (fun _ ↦ (1 : ℝ)) | hσ.measurableSpace] ≤ᵐ[μ]
      fun _ ↦ Real.exp (-lowerOccupationDecayRate c₀ * (r : ℝ)) := by
  have h := condExp_stoppedLowerOccupationEvent_le_finiteRange
    (θ := (1 : ℝ)) (a := lowerOccupationCountRate c₀) (r := r)
      (by norm_num) hC₀ hN hΛ hΛupper hσ hσ_range hσB hτ hΛlower
  have hexponent : lowerOccupationExponent 1 c₀ (lowerOccupationCountRate c₀) =
      lowerOccupationDecayRate c₀ := by
    simp only [lowerOccupationExponent, lowerOccupationCountRate,
      lowerOccupationDecayRate, one_mul]
    ring
  rw [hexponent] at h
  exact h

/-- Explicit `(1.39b)` bound from an arbitrary deterministically bounded stopping coordinate.
This is the grid-free C2 endpoint used by later crossing and return-time arguments. -/
theorem condExp_stoppedLowerOccupationEvent_le_explicit_boundedStopping
    {mu : Measure Ω} [IsFiniteMeasure mu]
    {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {N : ℝ≥0 → Ω → ℕ}
    {Lambda : ℝ≥0 → Ω → ℝ} {sigma : Ω → ℝ≥0} {tau : Ω → WithTop ℝ≥0}
    {c₀ C₀ : ℝ} {B r : ℝ≥0}
    (_hc₀ : 0 < c₀) (hC₀ : 0 ≤ C₀) (hr : 0 < r)
    (hN : IsSimpleCountingProcess F N)
    (hLambda : HasPredictableIntensity mu F N Lambda)
    (hLambdaUpper : ∀ u omega, Lambda u omega ≤ C₀)
    (hsigma : IsStoppingTime F fun omega ↦ (sigma omega : WithTop ℝ≥0))
    (hsigmaB : ∀ omega, sigma omega ≤ B) (htau : IsStoppingTime F tau)
    (hLambdaLower : ∀ (u : ℝ≥0) omega, (u : WithTop ℝ≥0) ≤ tau omega → c₀ ≤ Lambda u omega) :
    mu[(stoppedLowerOccupationEvent N sigma tau (lowerOccupationCountRate c₀) r).indicator
          (fun _ ↦ (1 : ℝ)) | hsigma.measurableSpace] ≤ᵐ[mu]
      fun _ ↦ Real.exp (-lowerOccupationDecayRate c₀ * (r : ℝ)) := by
  have h := condExp_stoppedLowerOccupationEvent_le_boundedStopping
    (theta := (1 : ℝ)) (a := lowerOccupationCountRate c₀) (r := r)
      (by norm_num) hC₀ hr hN hLambda hLambdaUpper hsigma hsigmaB htau hLambdaLower
  have hexponent : lowerOccupationExponent 1 c₀ (lowerOccupationCountRate c₀) =
      lowerOccupationDecayRate c₀ := by
    simp only [lowerOccupationExponent, lowerOccupationCountRate,
      lowerOccupationDecayRate, one_mul]
    ring
  rw [hexponent] at h
  exact h

/-- Unconditional form of the grid-free stopped occupation bound. -/
theorem measureReal_stoppedLowerOccupationEvent_le_explicit_boundedStopping
    {mu : Measure Ω} [IsProbabilityMeasure mu]
    {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {N : ℝ≥0 → Ω → ℕ}
    {Lambda : ℝ≥0 → Ω → ℝ} {sigma : Ω → ℝ≥0} {tau : Ω → WithTop ℝ≥0}
    {c₀ C₀ : ℝ} {B r : ℝ≥0}
    (hc₀ : 0 < c₀) (hC₀ : 0 ≤ C₀) (hr : 0 < r)
    (hN : IsSimpleCountingProcess F N)
    (hLambda : HasPredictableIntensity mu F N Lambda)
    (hLambdaUpper : ∀ u omega, Lambda u omega ≤ C₀)
    (hsigma : IsStoppingTime F fun omega ↦ (sigma omega : WithTop ℝ≥0))
    (hsigmaB : ∀ omega, sigma omega ≤ B) (htau : IsStoppingTime F tau)
    (hLambdaLower : ∀ (u : ℝ≥0) omega, (u : WithTop ℝ≥0) ≤ tau omega → c₀ ≤ Lambda u omega) :
    mu.real (stoppedLowerOccupationEvent N sigma tau (lowerOccupationCountRate c₀) r) ≤
      Real.exp (-lowerOccupationDecayRate c₀ * (r : ℝ)) := by
  have hcond := condExp_stoppedLowerOccupationEvent_le_explicit_boundedStopping
    hc₀ hC₀ hr hN hLambda hLambdaUpper hsigma hsigmaB htau hLambdaLower
  exact measureReal_le_of_condExp_indicator_le_const hsigma.measurableSpace_le
    (measurableSet_stoppedLowerOccupationEvent_bounded hN hsigma hsigmaB htau) hcond

/-- Deterministic-start specialization of `(1.39b)`.  This is the form consumed when an
increasing-matching edge is charged at a deterministic exploration coordinate. -/
theorem condExp_stoppedLowerOccupationEvent_le_const
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {N : ℝ≥0 → Ω → ℕ}
    {Λ : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}
    {c₀ C₀ : ℝ} {s r : ℝ≥0}
    (hc₀ : 0 < c₀) (hC₀ : 0 ≤ C₀) (hN : IsSimpleCountingProcess ℱ N)
    (hΛ : HasPredictableIntensity μ ℱ N Λ) (hΛupper : ∀ u ω, Λ u ω ≤ C₀)
    (hτ : IsStoppingTime ℱ τ)
    (hΛlower : ∀ (u : ℝ≥0) ω, (u : WithTop ℝ≥0) ≤ τ ω → c₀ ≤ Λ u ω) :
    μ[(stoppedLowerOccupationEvent N (fun _ ↦ s) τ
        (lowerOccupationCountRate c₀) r).indicator (fun _ ↦ (1 : ℝ)) |
          ℱ s] ≤ᵐ[μ]
      fun _ ↦ Real.exp (-lowerOccupationDecayRate c₀ * (r : ℝ)) := by
  have hσ : IsStoppingTime ℱ (fun _ : Ω ↦ (s : WithTop ℝ≥0)) :=
    MeasureTheory.isStoppingTime_const ℱ s
  have h := condExp_stoppedLowerOccupationEvent_le_explicit hc₀ hC₀ hN hΛ hΛupper
    (r := r) hσ Set.finite_range_const (fun _ ↦ le_rfl) hτ hΛlower
  rw [MeasureTheory.IsStoppingTime.measurableSpace_const ℱ s] at h
  exact h

end OTSelector.CountingProcess
