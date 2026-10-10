import OTSelector.Feedback.FeedbackBoundaryComparison
import OTSelector.Feedback.FiniteEventBulkOccupation

/-!
# Strict-stop lower occupation for the I3 rank-gap argument

The actual A1 rate bounds hold strictly before the first failure coordinate.  This is exactly
what the rank-gap argument needs: the right endpoint retained by the stopped lower-occupation
event contributes one time point, and `timeMeasure` has no atoms.  This file records the minimal
strict-stop variant of the existing lower-occupation theorem.  No new intensity or tail
hypothesis is introduced.
-/

open Filter Set
open scoped ENNReal NNReal MeasureTheory ProbabilityTheory Topology

namespace OTSelector.CountingProcess

open _root_.MeasureTheory

variable {Ω : Type*} [hΩ : MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
private theorem timeMeasure_singleton_zero_i3 (a : ℝ≥0) :
    timeMeasure ({a} : Set ℝ≥0) = 0 := by
  rw [timeMeasure, Measure.map_apply measurable_real_toNNReal
    (measurableSet_singleton a)]
  rw [Measure.restrict_apply (continuous_real_toNNReal.measurable
    (measurableSet_singleton a))]
  have hpre : Real.toNNReal ⁻¹' ({a} : Set ℝ≥0) ∩ Ici (0 : ℝ) =
      ({(a : ℝ)} : Set ℝ) := by
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_Ici]
    constructor
    · rintro ⟨hxa, hx0⟩
      have hxcoe : Real.toNNReal x = Real.toNNReal (a : ℝ) := by simpa using hxa
      exact Real.toNNReal_eq_toNNReal_iff hx0 a.2 |>.mp hxcoe
    · intro hxa
      subst x
      exact ⟨Real.toNNReal_coe, a.2⟩
  rw [hpre, Real.volume_singleton]

/-- A strict pathwise lower intensity bound gives the same compensator lower bound through a
closed deterministic endpoint.  The only missing point is the endpoint itself, which is null
for `timeMeasure`. -/
theorem integratedIntensity_one_sub_lower_strict
    {μ : Measure Ω} {F : Filtration ℝ≥0 hΩ} {N : ℝ≥0 → Ω → ℕ}
    {Lambda : ℝ≥0 → Ω → ℝ} (hLambda : HasPredictableIntensity μ F N Lambda)
    {s t : ℝ≥0} (hst : s ≤ t) {omega : Ω} {c₀ : ℝ}
    {tau : Ω → WithTop ℝ≥0} (htau : (t : WithTop ℝ≥0) ≤ tau omega)
    (hLower : ∀ u : ℝ≥0, ∀ omega, (u : WithTop ℝ≥0) < tau omega →
      c₀ ≤ Lambda u omega) :
    c₀ * ((t : ℝ) - (s : ℝ)) ≤
      integratedIntensity Lambda (fun _ _ ↦ (1 : ℝ)) t omega -
        integratedIntensity Lambda (fun _ _ ↦ (1 : ℝ)) s omega := by
  have hHI : IntervalIntegrable (fun x : ℝ ↦ Lambda (Real.toNNReal x) omega)
      volume 0 (t : ℝ) :=
    intervalIntegrable_toReal_of_integrableOn (hLambda.integrableOn t omega)
  have hadd := integratedIntensity_add_Ioc (H := fun _ _ ↦ (1 : ℝ))
    (w := 0) (v := s) (u := t) (by simp) hst (by simpa using hHI)
  have hA0 : integratedIntensity Lambda (fun _ _ ↦ (1 : ℝ)) 0 omega = 0 := by
    simp [integratedIntensity]
  have hAs : integratedIntensity Lambda (fun _ _ ↦ (1 : ℝ)) s omega =
      ∫ u in Ioc (0 : ℝ≥0) s, Lambda u omega ∂timeMeasure := by
    simp [integratedIntensity]
  have hdiff : integratedIntensity Lambda (fun _ _ ↦ (1 : ℝ)) t omega -
      integratedIntensity Lambda (fun _ _ ↦ (1 : ℝ)) s omega =
        ∫ u in Ioc s t, Lambda u omega ∂timeMeasure := by
    rw [hA0] at hadd
    simp only [zero_add, one_mul] at hadd
    rw [← hAs] at hadd
    linarith
  have hconstInt : IntegrableOn (fun _ : ℝ≥0 ↦ c₀) (Ioc s t) timeMeasure :=
    integrableOn_const (C := c₀) (timeMeasure_Ioc_lt_top s t).ne
  have hLambdaInt : IntegrableOn (fun u ↦ Lambda u omega) (Ioc s t) timeMeasure :=
    (hLambda.integrableOn t omega).mono_set fun u hu ↦
      ⟨lt_of_le_of_lt s.2 hu.1, hu.2⟩
  have hne : ∀ᵐ u : ℝ≥0 ∂timeMeasure, u ≠ t := by
    apply MeasureTheory.ae_iff.mpr
    simpa only [not_ne_iff, Set.ofPred_eq_eq_singleton] using
      timeMeasure_singleton_zero_i3 t
  have hae : ∀ᵐ u ∂timeMeasure.restrict (Ioc s t), c₀ ≤ Lambda u omega := by
    apply (ae_restrict_iff' measurableSet_Ioc).2
    filter_upwards [hne] with u hut hu
    have hutlt : u < t := lt_of_le_of_ne hu.2 hut
    exact hLower u omega ((WithTop.coe_lt_coe.mpr hutlt).trans_le htau)
  have hmono : (∫ u in Ioc s t, c₀ ∂timeMeasure) ≤
      ∫ u in Ioc s t, Lambda u omega ∂timeMeasure :=
    integral_mono_ae hconstInt hLambdaInt hae
  have hconst : (∫ _u in Ioc s t, c₀ ∂timeMeasure) =
      c₀ * ((t : ℝ) - (s : ℝ)) := by
    rw [integral_timeMeasure_eq_intervalIntegral (fun _ : ℝ≥0 ↦ c₀) s t
      (by exact_mod_cast hst)]
    rw [intervalIntegral.integral_const]
    ring
  rw [hdiff, ← hconst]
  exact hmono

/-- Finite-grid conditional lower occupation when the intensity lower bound is known only
strictly before the stopping coordinate. -/
theorem condExp_stoppedLowerOccupationEvent_le_finiteRange_strict
    {mu : Measure Ω} [IsFiniteMeasure mu]
    {F : Filtration ℝ≥0 hΩ} {N : ℝ≥0 → Ω → ℕ}
    {Lambda : ℝ≥0 → Ω → ℝ} {sigma : Ω → ℝ≥0} {tau : Ω → WithTop ℝ≥0}
    {theta c₀ C₀ a : ℝ} {B r : ℝ≥0}
    (htheta : 0 < theta) (hC₀ : 0 ≤ C₀) (hN : IsSimpleCountingProcess F N)
    (hLambda : HasPredictableIntensity mu F N Lambda)
    (hLambdaUpper : ∀ u omega, Lambda u omega ≤ C₀)
    (hsigma : IsStoppingTime F fun omega ↦ (sigma omega : WithTop ℝ≥0))
    (hsigmaRange : (Set.range sigma).Finite) (hsigmaB : ∀ omega, sigma omega ≤ B)
    (htau : IsStoppingTime F tau)
    (hLambdaLower : ∀ (u : ℝ≥0) omega, (u : WithTop ℝ≥0) < tau omega →
      c₀ ≤ Lambda u omega) :
    mu[(stoppedLowerOccupationEvent N sigma tau a r).indicator (fun _ ↦ (1 : ℝ)) |
        hsigma.measurableSpace] ≤ᵐ[mu]
      fun _ ↦ Real.exp (-lowerOccupationExponent theta c₀ a * (r : ℝ)) := by
  let T : ℝ≥0 := B + r
  let Z : ℝ≥0 → Ω → ℝ := finiteHorizonCountingExponential N Lambda theta T
  let rho : Ω → ℝ≥0 := fun omega ↦ sigma omega + r
  let X : Ω → ℝ := fun omega ↦ Z (sigma omega) omega
  let Y : Ω → ℝ := fun omega ↦ Z (rho omega) omega
  let R : ℝ := Real.exp (lowerOccupationExponent theta c₀ a * (r : ℝ))
  have hM : Martingale Z F mu :=
    finiteHorizonCountingExponential_martingale
      htheta hC₀ hLambdaUpper hN hLambda
  have hrho := IsStoppingTime.coe_add_const_finiteRange hsigma hsigmaRange r
  have hsigmaT : ∀ omega, (sigma omega : WithTop ℝ≥0) ≤ T := by
    intro omega
    exact_mod_cast (hsigmaB omega).trans (le_add_right (le_refl B))
  have hrhoT : ∀ omega, (rho omega : WithTop ℝ≥0) ≤ T := by
    intro omega
    change ((sigma omega + r : ℝ≥0) : WithTop ℝ≥0) ≤ (B + r : ℝ≥0)
    exact_mod_cast (by simpa [add_comm] using add_le_add_right (hsigmaB omega) r)
  have hsigmarho : ∀ omega, (sigma omega : WithTop ℝ≥0) ≤ rho omega := by
    intro omega
    exact_mod_cast le_add_right (le_refl (sigma omega))
  have hsigmaCoeRange : (Set.range fun omega ↦ (sigma omega : WithTop ℝ≥0)).Finite := by
    rw [show (fun omega ↦ (sigma omega : WithTop ℝ≥0)) =
      (fun s : ℝ≥0 ↦ (s : WithTop ℝ≥0)) ∘ sigma by rfl, Set.range_comp]
    exact hsigmaRange.image fun s : ℝ≥0 ↦ (s : WithTop ℝ≥0)
  have hrhoRange : (Set.range rho).Finite := by
    rw [show rho = (fun s : ℝ≥0 ↦ s + r) ∘ sigma by rfl, Set.range_comp]
    exact hsigmaRange.image fun s : ℝ≥0 ↦ s + r
  have hCEraw := hM.stoppedValue_ae_eq_condExp_of_le_of_countable_range
    hrho.1 hsigma hsigmarho hrhoT hrho.2.countable hsigmaCoeRange.countable
  have hstopSigma : stoppedValue Z (fun omega ↦ (sigma omega : WithTop ℝ≥0)) = X := by
    funext omega
    unfold stoppedValue
    rw [WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
  have hstopRho : stoppedValue Z
      (fun omega ↦ ((sigma omega + r : ℝ≥0) : WithTop ℝ≥0)) = Y := by
    funext omega
    unfold stoppedValue
    rw [WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
  have hCE : mu[Y | hsigma.measurableSpace] =ᵐ[mu] X := by
    rw [hstopSigma, hstopRho] at hCEraw
    exact hCEraw.symm
  have hE := measurableSet_stoppedLowerOccupationEvent_finiteRange
    (a := a) (r := r) hN hsigma hsigmaRange htau
  have hYmeas : StronglyMeasurable Y := by
    apply stronglyMeasurable_eval_finiteRange hM.stronglyAdapted hrho.1 hrhoRange
  have hYint : Integrable Y mu := by
    apply Integrable.mono' (integrable_const
      (Real.exp ((1 - Real.exp (-theta)) * C₀ * (T : ℝ))))
    · exact hYmeas.aestronglyMeasurable
    · filter_upwards with omega
      have hnonneg : 0 ≤ Y omega :=
        (countingExponential_pos N Lambda (fun _ _ ↦ -theta)
          (min (rho omega) T) omega).le
      have hupper : Y omega ≤
          Real.exp ((1 - Real.exp (-theta)) * C₀ * (T : ℝ)) := by
        dsimp [Y, Z, finiteHorizonCountingExponential]
        exact countingExponential_const_neg_le hLambda htheta hC₀ hLambdaUpper
          (min_le_right (rho omega) T) omega
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg,
        abs_of_pos (Real.exp_pos _)] using hupper
  have hscaled : ∀ omega ∈ stoppedLowerOccupationEvent N sigma tau a r,
      R * X omega ≤ Y omega := by
    intro omega homega
    have hst : sigma omega ≤ rho omega := le_add_right (le_refl (sigma omega))
    have hA := integratedIntensity_one_sub_lower_strict hLambda hst homega.2 hLambdaLower
    have hcount : (N (rho omega) omega : ℝ) - N (sigma omega) omega ≤
        a * ((rho omega : ℝ) - (sigma omega : ℝ)) := by
      simpa [rho] using homega.1
    have hpath := countingExponential_interval_lower hLambda htheta hcount hA
    simpa [R, X, Y, Z, finiteHorizonCountingExponential, rho,
      min_eq_left (show sigma omega ≤ T by exact_mod_cast hsigmaT omega),
      min_eq_left (show rho omega ≤ T by exact_mod_cast hrhoT omega)] using hpath
  have hXpos : ∀ omega, 0 < X omega := fun omega ↦
    countingExponential_pos N Lambda (fun _ _ ↦ -theta)
      (min (sigma omega) T) omega
  have hYnonneg : ∀ omega, 0 ≤ Y omega := fun omega ↦
    (countingExponential_pos N Lambda (fun _ _ ↦ -theta)
      (min (rho omega) T) omega).le
  have hmarkov := condExp_indicator_le_inv_of_scaled hE (Real.exp_pos _)
    hXpos hYnonneg hscaled hYint hCE
  filter_upwards [hmarkov] with omega homega
  rw [show -lowerOccupationExponent theta c₀ a * (r : ℝ) =
    -(lowerOccupationExponent theta c₀ a * (r : ℝ)) by ring, Real.exp_neg]
  exact homega

/-- Arbitrary bounded stopping starts, with the rate lower bound required only strictly before
the terminal stopping coordinate. -/
theorem condExp_stoppedLowerOccupationEvent_le_boundedStopping_strict
    {mu : Measure Ω} [IsFiniteMeasure mu]
    {F : Filtration ℝ≥0 hΩ} {N : ℝ≥0 → Ω → ℕ}
    {Lambda : ℝ≥0 → Ω → ℝ} {sigma : Ω → ℝ≥0} {tau : Ω → WithTop ℝ≥0}
    {theta c₀ C₀ a : ℝ} {B r : ℝ≥0}
    (htheta : 0 < theta) (hC₀ : 0 ≤ C₀) (hr : 0 < r)
    (hN : IsSimpleCountingProcess F N)
    (hLambda : HasPredictableIntensity mu F N Lambda)
    (hLambdaUpper : ∀ u omega, Lambda u omega ≤ C₀)
    (hsigma : IsStoppingTime F fun omega ↦ (sigma omega : WithTop ℝ≥0))
    (hsigmaB : ∀ omega, sigma omega ≤ B) (htau : IsStoppingTime F tau)
    (hLambdaLower : ∀ (u : ℝ≥0) omega, (u : WithTop ℝ≥0) < tau omega →
      c₀ ≤ Lambda u omega) :
    mu[(stoppedLowerOccupationEvent N sigma tau a r).indicator (fun _ ↦ (1 : ℝ)) |
        hsigma.measurableSpace] ≤ᵐ[mu]
      fun _ ↦ Real.exp (-lowerOccupationExponent theta c₀ a * (r : ℝ)) := by
  let mesh : ℕ → ℝ≥0 := fun k ↦ (((k + 1 : ℕ) : ℝ≥0))⁻¹
  let short : ℕ → ℝ≥0 := fun k ↦ r - mesh k
  let bound : ℕ → ℝ := fun k ↦
    Real.exp (-((1 - Real.exp (-theta)) * c₀ * (short k : ℝ) -
      theta * a * (r : ℝ)))
  have hmeshTendsto : Tendsto mesh atTop (nhds 0) :=
    (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ≥0)).comp (tendsto_add_atTop_nat 1)
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
        tendsto_const_nhds).neg) using 1
      all_goals simp [lowerOccupationExponent]
      all_goals ring
    exact Real.continuous_exp.continuousAt.tendsto.comp hlinear
  have hE : MeasurableSet (stoppedLowerOccupationEvent N sigma tau a r) :=
    measurableSet_stoppedLowerOccupationEvent_bounded hN hsigma hsigmaB htau
  have honeGrid : ∀ k, mesh k < r →
      mu[(stoppedLowerOccupationEvent N sigma tau a r).indicator (fun _ ↦ (1 : ℝ)) |
          hsigma.measurableSpace] ≤ᵐ[mu] fun _ ↦ bound k := by
    intro k hmesh
    let sigmak : Ω → ℝ≥0 := fun omega ↦ rightGrid (k + 1) (sigma omega)
    let ratek : ℝ := a * (r : ℝ) / (short k : ℝ)
    have hsigmak : IsStoppingTime F fun omega ↦ (sigmak omega : WithTop ℝ≥0) :=
      IsStoppingTime.rightGridApprox hsigma (k + 1) (by omega)
    have hsigmakRange : (Set.range sigmak).Finite :=
      finiteRange_rightGrid_of_le (k + 1) (by omega) hsigmaB
    have hsigmakB : ∀ omega, sigmak omega ≤ B + mesh k := by
      intro omega
      exact (rightGrid_lt_add_inv (k + 1) (sigma omega) (by omega)).le.trans
        (add_le_add_left (hsigmaB omega) (mesh k))
    have hgrid := condExp_stoppedLowerOccupationEvent_le_finiteRange_strict
      (theta := theta) (c₀ := c₀) (C₀ := C₀) (a := ratek)
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
    · exact (honeGrid k hk).mono fun omega homega _ ↦ homega
    · exact Eventually.of_forall fun _ hk' ↦ (hk hk').elim
  filter_upwards [hAll] with omega homega
  apply ge_of_tendsto hboundTendsto
  filter_upwards [(tendsto_order.1 hmeshTendsto).2 r hr] with k hk
  exact homega k hk

/-- Explicit strict-stop form of the lower-occupation estimate. -/
theorem condExp_stoppedLowerOccupationEvent_le_explicit_boundedStopping_strict
    {mu : Measure Ω} [IsFiniteMeasure mu]
    {F : Filtration ℝ≥0 hΩ} {N : ℝ≥0 → Ω → ℕ}
    {Lambda : ℝ≥0 → Ω → ℝ} {sigma : Ω → ℝ≥0} {tau : Ω → WithTop ℝ≥0}
    {c₀ C₀ : ℝ} {B r : ℝ≥0}
    (_hc₀ : 0 < c₀) (hC₀ : 0 ≤ C₀) (hr : 0 < r)
    (hN : IsSimpleCountingProcess F N)
    (hLambda : HasPredictableIntensity mu F N Lambda)
    (hLambdaUpper : ∀ u omega, Lambda u omega ≤ C₀)
    (hsigma : IsStoppingTime F fun omega ↦ (sigma omega : WithTop ℝ≥0))
    (hsigmaB : ∀ omega, sigma omega ≤ B) (htau : IsStoppingTime F tau)
    (hLambdaLower : ∀ (u : ℝ≥0) omega, (u : WithTop ℝ≥0) < tau omega →
      c₀ ≤ Lambda u omega) :
    mu[(stoppedLowerOccupationEvent N sigma tau (lowerOccupationCountRate c₀) r).indicator
        (fun _ ↦ (1 : ℝ)) | hsigma.measurableSpace] ≤ᵐ[mu]
      fun _ ↦ Real.exp (-lowerOccupationDecayRate c₀ * (r : ℝ)) := by
  have h := condExp_stoppedLowerOccupationEvent_le_boundedStopping_strict
    (theta := (1 : ℝ)) (a := lowerOccupationCountRate c₀) (r := r)
    (c₀ := c₀) (C₀ := C₀) (by norm_num) hC₀ hr hN hLambda hLambdaUpper
    hsigma hsigmaB htau hLambdaLower
  have hexponent : lowerOccupationExponent 1 c₀ (lowerOccupationCountRate c₀) =
      lowerOccupationDecayRate c₀ := by
    simp only [lowerOccupationExponent, lowerOccupationCountRate,
      lowerOccupationDecayRate, one_mul]
    ring
  simpa only [hexponent] using h

end OTSelector.CountingProcess

namespace OTSelector.FiniteSample

open CountingProcess
open MeasureTheory

variable {n : ℕ}

/-- Actual source lower occupation through the A1 coordinate, using the genuine strict
`[1/2,3]` source-rate bound. -/
theorem safeSourceBulkCount_condExp_lowerOccupation_through_A1
    {lam eta B x0 p0 : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hn : 0 < n) (hB : 0 < B) (heta0 : 0 ≤ eta)
    (hetaSmall : eta * (2 + lam) ≤ lam) (T : ℝ≥0)
    {sigma : FiniteSample n → ℝ≥0} {S r : ℝ≥0} (hr : 0 < r)
    (hsigma : IsStoppingTime
      (usualRevealedFiltration (n := n) hlam0.le (by linarith) x0 p0)
      (fun sample ↦ (sigma sample : WithTop ℝ≥0)))
    (hsigmaS : ∀ sample, sigma sample ≤ S) :
    condExp hsigma.measurableSpace
        (finiteSampleLaw n : Measure (FiniteSample n))
        ((stoppedLowerOccupationEvent
          (safeSourceBulkCount (n := n) hlam0.le (by linarith) B x0 p0)
          sigma (safeFeedbackA1StopTime
            (n := n) hlam0.le (by linarith) eta B x0 p0 T)
          (lowerOccupationCountRate ((1 : ℝ) / 2)) r).indicator
            (fun _ ↦ (1 : ℝ))) ≤ᵐ[(finiteSampleLaw n : Measure (FiniteSample n))]
      fun _ ↦ Real.exp (-lowerOccupationDecayRate ((1 : ℝ) / 2) * (r : ℝ)) := by
  let hlamHalf : lam < 1 / 2 := by linarith
  exact condExp_stoppedLowerOccupationEvent_le_explicit_boundedStopping_strict
    (mu := finiteSampleLaw n)
    (F := usualRevealedFiltration (n := n) hlam0.le hlamHalf x0 p0)
    (N := safeSourceBulkCount hlam0.le hlamHalf B x0 p0)
    (Lambda := safeSourceBulkRate hlam0.le hlamHalf B x0 p0)
    (sigma := sigma)
    (tau := safeFeedbackA1StopTime hlam0.le hlamHalf eta B x0 p0 T)
    (c₀ := (1 : ℝ) / 2) (C₀ := feedbackBulkRateCap n B)
    (B := S) (r := r) (by norm_num) (feedbackBulkRateCap_nonneg n B) hr
    (safeSourceBulkCount_isSimpleCountingProcess
      (n := n) hlam0.le hlamHalf B x0 p0)
    (safeSourceBulkCount_hasPredictableIntensity
      (n := n) hlam0.le hlamHalf hn hB)
    (fun u sample ↦ safeSourceBulkRate_le_cap
      hlam0.le hlamHalf B x0 p0 u sample)
    hsigma hsigmaS
    (safeFeedbackA1StopTime_isStoppingTime
      (n := n) hlam0.le hlamHalf hB eta x0 p0 T)
    (fun u sample hu ↦
      (safeSourceBulkRate_mem_Icc_of_lt_A1Stop
        (n := n) hlam0 hlam hB heta0 hetaSmall T u sample hu).1)

/-- Actual target lower occupation through the A1 coordinate, using the genuine strict
`[1/2,3]` target-rate bound. -/
theorem safeTargetBulkCount_condExp_lowerOccupation_through_A1
    {lam eta B x0 p0 : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hn : 0 < n) (hB : 0 < B) (heta0 : 0 ≤ eta)
    (hetaSmall : eta * (2 + lam) ≤ lam) (T : ℝ≥0)
    {sigma : FiniteSample n → ℝ≥0} {S r : ℝ≥0} (hr : 0 < r)
    (hsigma : IsStoppingTime
      (usualRevealedFiltration (n := n) hlam0.le (by linarith) x0 p0)
      (fun sample ↦ (sigma sample : WithTop ℝ≥0)))
    (hsigmaS : ∀ sample, sigma sample ≤ S) :
    condExp hsigma.measurableSpace
        (finiteSampleLaw n : Measure (FiniteSample n))
        ((stoppedLowerOccupationEvent
          (safeTargetBulkCount (n := n) hlam0.le (by linarith) B x0 p0)
          sigma (safeFeedbackA1StopTime
            (n := n) hlam0.le (by linarith) eta B x0 p0 T)
          (lowerOccupationCountRate ((1 : ℝ) / 2)) r).indicator
            (fun _ ↦ (1 : ℝ))) ≤ᵐ[(finiteSampleLaw n : Measure (FiniteSample n))]
      fun _ ↦ Real.exp (-lowerOccupationDecayRate ((1 : ℝ) / 2) * (r : ℝ)) := by
  let hlamHalf : lam < 1 / 2 := by linarith
  exact condExp_stoppedLowerOccupationEvent_le_explicit_boundedStopping_strict
    (mu := finiteSampleLaw n)
    (F := usualRevealedFiltration (n := n) hlam0.le hlamHalf x0 p0)
    (N := safeTargetBulkCount hlam0.le hlamHalf B x0 p0)
    (Lambda := safeTargetBulkRate hlam0.le hlamHalf B x0 p0)
    (sigma := sigma)
    (tau := safeFeedbackA1StopTime hlam0.le hlamHalf eta B x0 p0 T)
    (c₀ := (1 : ℝ) / 2) (C₀ := feedbackBulkRateCap n B)
    (B := S) (r := r) (by norm_num) (feedbackBulkRateCap_nonneg n B) hr
    (safeTargetBulkCount_isSimpleCountingProcess
      (n := n) hlam0.le hlamHalf B x0 p0)
    (safeTargetBulkCount_hasPredictableIntensity
      (n := n) hlam0.le hlamHalf hn hB)
    (fun u sample ↦ safeTargetBulkRate_le_cap
      hlam0.le hlamHalf B x0 p0 u sample)
    hsigma hsigmaS
    (safeFeedbackA1StopTime_isStoppingTime
      (n := n) hlam0.le hlamHalf hB eta x0 p0 T)
    (fun u sample hu ↦
      (safeTargetBulkRate_mem_Icc_of_lt_A1Stop
        (n := n) hlam0 hlam hB heta0 hetaSmall T u sample hu).1)

end OTSelector.FiniteSample
