import OTSelector.Feedback.MarkedPredictable
import OTSelector.Feedback.MarkedStoppedOccupation
import OTSelector.Probability.CountingProcess.MarkedChainRule

/-!
# Stopped two-colour current excursions

This file controls a stopped nearest-neighbour current by counting outward jumps in the two
bands between radii `R` and `2 * R`.  The counting transforms use the strict-left current and a
right-closed through-stop mask, hence include an exit jump at the stopping coordinate.
-/

open Set
open scoped ENNReal NNReal MeasureTheory ProbabilityTheory

namespace OTSelector.CountingProcess

open _root_.MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## A finite potential for the two outward bands -/

/-- Number of positive band levels already crossed by the integer current. -/
def positiveBandPotential (R : ℕ) (k : ℤ) : ℕ :=
  min R (k - R).toNat

/-- Number of negative band levels already crossed by the integer current. -/
def negativeBandPotential (R : ℕ) (k : ℤ) : ℕ :=
  min R (-k - R).toNat

/-- Total number of positive or negative band levels crossed by the current. -/
def outwardBandPotential (R : ℕ) (k : ℤ) : ℝ :=
  positiveBandPotential R k + negativeBandPotential R k

/-- Indicator for an upward jump whose left state lies in the positive outward band. -/
def positiveOutwardBand (R : ℕ) (k : ℤ) : ℝ :=
  if (R : ℤ) ≤ k ∧ k < 2 * (R : ℤ) then 1 else 0

/-- Indicator for a downward jump whose left state lies in the negative outward band. -/
def negativeOutwardBand (R : ℕ) (k : ℤ) : ℝ :=
  if -(2 * (R : ℤ)) < k ∧ k ≤ -(R : ℤ) then 1 else 0

omit [MeasurableSpace Ω] in
private theorem positiveBandPotential_up_sub_le (R : ℕ) (k : ℤ) :
    (positiveBandPotential R (k + 1) : ℤ) - positiveBandPotential R k ≤
      if (R : ℤ) ≤ k ∧ k < 2 * (R : ℤ) then 1 else 0 := by
  simp only [positiveBandPotential]
  split_ifs <;> omega

omit [MeasurableSpace Ω] in
private theorem negativeBandPotential_up_sub_le (R : ℕ) (k : ℤ) :
    (negativeBandPotential R (k + 1) : ℤ) - negativeBandPotential R k ≤ 0 := by
  simp only [negativeBandPotential]
  omega

omit [MeasurableSpace Ω] in
private theorem positiveBandPotential_down_sub_le (R : ℕ) (k : ℤ) :
    (positiveBandPotential R (k - 1) : ℤ) - positiveBandPotential R k ≤ 0 := by
  simp only [positiveBandPotential]
  omega

omit [MeasurableSpace Ω] in
private theorem negativeBandPotential_down_sub_le (R : ℕ) (k : ℤ) :
    (negativeBandPotential R (k - 1) : ℤ) - negativeBandPotential R k ≤
      if -(2 * (R : ℤ)) < k ∧ k ≤ -(R : ℤ) then 1 else 0 := by
  simp only [negativeBandPotential]
  split_ifs <;> omega

omit [MeasurableSpace Ω] in
theorem outwardBandPotential_up_sub_le (R : ℕ) (k : ℤ) :
    outwardBandPotential R (k + 1) - outwardBandPotential R k ≤
      positiveOutwardBand R k := by
  dsimp only [outwardBandPotential, positiveOutwardBand]
  have hp : (positiveBandPotential R (k + 1) : ℝ) -
      positiveBandPotential R k ≤
        if (R : ℤ) ≤ k ∧ k < 2 * (R : ℤ) then 1 else 0 := by
    exact_mod_cast positiveBandPotential_up_sub_le R k
  have hn : (negativeBandPotential R (k + 1) : ℝ) -
      negativeBandPotential R k ≤ 0 := by
    exact_mod_cast negativeBandPotential_up_sub_le R k
  linarith

omit [MeasurableSpace Ω] in
theorem outwardBandPotential_down_sub_le (R : ℕ) (k : ℤ) :
    outwardBandPotential R (k - 1) - outwardBandPotential R k ≤
      negativeOutwardBand R k := by
  dsimp only [outwardBandPotential, negativeOutwardBand]
  have hp : (positiveBandPotential R (k - 1) : ℝ) -
      positiveBandPotential R k ≤ 0 := by
    exact_mod_cast positiveBandPotential_down_sub_le R k
  have hn : (negativeBandPotential R (k - 1) : ℝ) -
      negativeBandPotential R k ≤
        if -(2 * (R : ℤ)) < k ∧ k ≤ -(R : ℤ) then 1 else 0 := by
    exact_mod_cast negativeBandPotential_down_sub_le R k
  linarith

omit [MeasurableSpace Ω] in
theorem outwardBandPotential_eq_zero_of_abs_lt
    {R : ℕ} {k : ℤ} (hk : |(k : ℝ)| < R) :
    outwardBandPotential R k = 0 := by
  have hk' : -(R : ℤ) < k ∧ k < (R : ℤ) := by
    rw [abs_lt] at hk
    constructor
    · exact_mod_cast hk.1
    · exact_mod_cast hk.2
  simp only [outwardBandPotential, positiveBandPotential, negativeBandPotential]
  have hp : (k - (R : ℤ)).toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
  have hn : (-k - (R : ℤ)).toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
  rw [hp, hn]
  norm_num

omit [MeasurableSpace Ω] in
theorem outwardBandPotential_eq_radius_of_two_mul_le_abs
    {R : ℕ} {k : ℤ} (hk : 2 * (R : ℝ) ≤ |(k : ℝ)|) :
    outwardBandPotential R k = R := by
  by_cases hk0 : 0 ≤ k
  · have hkpos : (2 * R : ℤ) ≤ k := by
      rw [abs_of_nonneg (by exact_mod_cast hk0)] at hk
      exact_mod_cast hk
    have hpos : positiveBandPotential R k = R := by
      simp only [positiveBandPotential]
      apply min_eq_left
      omega
    have hneg : negativeBandPotential R k = 0 := by
      simp only [negativeBandPotential]
      rw [Int.toNat_eq_zero.mpr (by omega)]
      norm_num
    simp [outwardBandPotential, hpos, hneg]
  · have hkneg : k ≤ -(2 * R : ℤ) := by
      have hk0' : (k : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge hk0)
      rw [abs_of_nonpos hk0'] at hk
      have hkInt : (2 * R : ℤ) ≤ -k := by exact_mod_cast hk
      omega
    have hpos : positiveBandPotential R k = 0 := by
      simp only [positiveBandPotential]
      rw [Int.toNat_eq_zero.mpr (by omega)]
      norm_num
    have hneg : negativeBandPotential R k = R := by
      simp only [negativeBandPotential]
      apply min_eq_left
      omega
    simp [outwardBandPotential, hpos, hneg]

/-! ## Predictable outward-band counts -/

/-- Upward outward-band transform, localized through the right-closed stopping mask. -/
noncomputable def positiveOutwardBandIntegrand
    (τ : Ω → WithTop ℝ≥0) (R : ℕ) (K0 : Ω → ℤ)
    (Nplus Nminus : ℝ≥0 → Ω → ℕ) : ℝ≥0 → Ω → ℝ :=
  fun s ω ↦ throughStopMask τ s ω *
    positiveOutwardBand R (leftCurrentOfCounts K0 Nplus Nminus s ω)

/-- Downward outward-band transform, localized through the right-closed stopping mask. -/
noncomputable def negativeOutwardBandIntegrand
    (τ : Ω → WithTop ℝ≥0) (R : ℕ) (K0 : Ω → ℤ)
    (Nplus Nminus : ℝ≥0 → Ω → ℕ) : ℝ≥0 → Ω → ℝ :=
  fun s ω ↦ throughStopMask τ s ω *
    negativeOutwardBand R (leftCurrentOfCounts K0 Nplus Nminus s ω)

/-- Total number of localized outward jumps from both colours. -/
noncomputable def throughStopOutwardBandCount
    (τ : Ω → WithTop ℝ≥0) (R : ℕ) (K0 : Ω → ℤ)
    (Nplus Nminus : ℝ≥0 → Ω → ℕ) (T : ℝ≥0) (ω : Ω) : ℝ :=
  countingIntegral Nplus
      (positiveOutwardBandIntegrand τ R K0 Nplus Nminus) T ω +
    countingIntegral Nminus
      (negativeOutwardBandIntegrand τ R K0 Nplus Nminus) T ω

theorem positiveOutwardBand_boundedSimplePredictable
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {K0 : Ω → ℤ} {Nplus Nminus : ℝ≥0 → Ω → ℕ}
    (hplus : IsSimpleCountingProcess ℱ Nplus)
    (hminus : IsSimpleCountingProcess ℱ Nminus)
    (hK0 : StronglyMeasurable[ℱ 0] (fun ω ↦ (K0 ω : ℝ))) (R : ℕ) :
    IsBoundedSimplePredictable ℱ
      (fun s ω ↦ positiveOutwardBand R
        (leftCurrentOfCounts K0 Nplus Nminus s ω)) := by
  apply IsBoundedSimplePredictable.of_binary_mask
    (leftCurrentOfCounts_comp_predictable hplus hminus hK0
      (positiveOutwardBand R))
  intro s ω
  simp only [positiveOutwardBand]
  split_ifs <;> simp

theorem negativeOutwardBand_boundedSimplePredictable
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {K0 : Ω → ℤ} {Nplus Nminus : ℝ≥0 → Ω → ℕ}
    (hplus : IsSimpleCountingProcess ℱ Nplus)
    (hminus : IsSimpleCountingProcess ℱ Nminus)
    (hK0 : StronglyMeasurable[ℱ 0] (fun ω ↦ (K0 ω : ℝ))) (R : ℕ) :
    IsBoundedSimplePredictable ℱ
      (fun s ω ↦ negativeOutwardBand R
        (leftCurrentOfCounts K0 Nplus Nminus s ω)) := by
  apply IsBoundedSimplePredictable.of_binary_mask
    (leftCurrentOfCounts_comp_predictable hplus hminus hK0
      (negativeOutwardBand R))
  intro s ω
  simp only [negativeOutwardBand]
  split_ifs <;> simp

theorem positiveOutwardBandIntegrand_boundedSimplePredictable
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {K0 : Ω → ℤ} {Nplus Nminus : ℝ≥0 → Ω → ℕ}
    {τ : Ω → WithTop ℝ≥0}
    (hplus : IsSimpleCountingProcess ℱ Nplus)
    (hminus : IsSimpleCountingProcess ℱ Nminus)
    (hK0 : StronglyMeasurable[ℱ 0] (fun ω ↦ (K0 ω : ℝ)))
    (hMask : IsBoundedSimplePredictable ℱ (throughStopMask τ)) (R : ℕ) :
    IsBoundedSimplePredictable ℱ
      (positiveOutwardBandIntegrand τ R K0 Nplus Nminus) := by
  change IsBoundedSimplePredictable ℱ (fun s ω ↦
    throughStopMask τ s ω * positiveOutwardBand R
      (leftCurrentOfCounts K0 Nplus Nminus s ω))
  exact hMask.mul_process
    (positiveOutwardBand_boundedSimplePredictable hplus hminus hK0 R)

theorem negativeOutwardBandIntegrand_boundedSimplePredictable
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {K0 : Ω → ℤ} {Nplus Nminus : ℝ≥0 → Ω → ℕ}
    {τ : Ω → WithTop ℝ≥0}
    (hplus : IsSimpleCountingProcess ℱ Nplus)
    (hminus : IsSimpleCountingProcess ℱ Nminus)
    (hK0 : StronglyMeasurable[ℱ 0] (fun ω ↦ (K0 ω : ℝ)))
    (hMask : IsBoundedSimplePredictable ℱ (throughStopMask τ)) (R : ℕ) :
    IsBoundedSimplePredictable ℱ
      (negativeOutwardBandIntegrand τ R K0 Nplus Nminus) := by
  change IsBoundedSimplePredictable ℱ (fun s ω ↦
    throughStopMask τ s ω * negativeOutwardBand R
      (leftCurrentOfCounts K0 Nplus Nminus s ω))
  exact hMask.mul_process
    (negativeOutwardBand_boundedSimplePredictable hplus hminus hK0 R)

omit [MeasurableSpace Ω] in
private theorem countingIntegral_le_throughStop_of_le
    {N : ℝ≥0 → Ω → ℕ} {H : ℝ≥0 → Ω → ℝ}
    (hmono : ∀ ω, Monotone fun t ↦ N t ω)
    (hH : ∀ s ω, 0 ≤ H s ω) (τ : Ω → WithTop ℝ≥0)
    {u T : ℝ≥0} {ω : Ω} (huT : u ≤ T)
    (huτ : (u : WithTop ℝ≥0) ≤ τ ω) :
    countingIntegral N H u ω ≤
      countingIntegral N (fun s ω' ↦ throughStopMask τ s ω' * H s ω') T ω := by
  have hNuT : N u ω ≤ N T ω := hmono ω huT
  unfold countingIntegral
  calc
    ∑ k ∈ Finset.range (N u ω), H (jumpTime N k ω) ω =
        ∑ k ∈ Finset.range (N u ω),
          throughStopMask τ (jumpTime N k ω) ω * H (jumpTime N k ω) ω := by
      apply Finset.sum_congr rfl
      intro k hk
      have hjump : jumpTime N k ω ≤ u := jumpTime_le_of_lt (Finset.mem_range.mp hk)
      have hjumpτ : (jumpTime N k ω : WithTop ℝ≥0) ≤ τ ω :=
        (WithTop.coe_le_coe.mpr hjump).trans huτ
      simp only [throughStopMask, ite_eq_left hjumpτ, one_mul]
    _ ≤ ∑ k ∈ Finset.range (N T ω),
          throughStopMask τ (jumpTime N k ω) ω * H (jumpTime N k ω) ω := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hNuT)
      intro k hkT hku
      by_cases hkτ : (jumpTime N k ω : WithTop ℝ≥0) ≤ τ ω
      · simp only [throughStopMask, ite_eq_left hkτ, one_mul]
        exact hH _ _
      · simp only [throughStopMask, ite_eq_right hkτ, zero_mul]
        exact le_rfl

theorem radius_le_throughStopOutwardBandCount_of_reaches
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {K0 : Ω → ℤ} {Nplus Nminus : ℝ≥0 → Ω → ℕ}
    (hplus : IsSimpleCountingProcess ℱ Nplus)
    (hminus : IsSimpleCountingProcess ℱ Nminus)
    {τ : Ω → WithTop ℝ≥0} {R : ℕ} {u T : ℝ≥0} {ω : Ω}
    (hNo : NoSimultaneousJumpsOn Nplus Nminus u)
    (huT : u ≤ T) (huτ : (u : WithTop ℝ≥0) ≤ τ ω)
    (hinitial : |(K0 ω : ℝ)| < R)
    (hreaches : 2 * (R : ℝ) ≤
      |(currentOfCounts K0 Nplus Nminus u ω : ℝ)|) :
    (R : ℝ) ≤ throughStopOutwardBandCount τ R K0 Nplus Nminus T ω := by
  let F : ℤ → ℝ := outwardBandPotential R
  have hchain := currentOfCounts_chain_rule
    (K0 := K0) hplus hminus hNo F ω
  have hplusStep : countingIntegral Nplus
      (fun s ω' ↦ F (leftCurrentOfCounts K0 Nplus Nminus s ω' + 1) -
        F (leftCurrentOfCounts K0 Nplus Nminus s ω')) u ω ≤
      countingIntegral Nplus
        (fun s ω' ↦ positiveOutwardBand R
          (leftCurrentOfCounts K0 Nplus Nminus s ω')) u ω := by
    unfold countingIntegral
    apply Finset.sum_le_sum
    intro k hk
    exact outwardBandPotential_up_sub_le R
      (leftCurrentOfCounts K0 Nplus Nminus (jumpTime Nplus k ω) ω)
  have hminusStep : countingIntegral Nminus
      (fun s ω' ↦ F (leftCurrentOfCounts K0 Nplus Nminus s ω' - 1) -
        F (leftCurrentOfCounts K0 Nplus Nminus s ω')) u ω ≤
      countingIntegral Nminus
        (fun s ω' ↦ negativeOutwardBand R
          (leftCurrentOfCounts K0 Nplus Nminus s ω')) u ω := by
    unfold countingIntegral
    apply Finset.sum_le_sum
    intro k hk
    exact outwardBandPotential_down_sub_le R
      (leftCurrentOfCounts K0 Nplus Nminus (jumpTime Nminus k ω) ω)
  have hterminal : F (currentOfCounts K0 Nplus Nminus u ω) = (R : ℝ) := by
    simpa only [F] using
      (outwardBandPotential_eq_radius_of_two_mul_le_abs
        (R := R) (k := currentOfCounts K0 Nplus Nminus u ω) hreaches)
  have hinitialPotential : F (K0 ω) = 0 := by
    simpa only [F] using
      (outwardBandPotential_eq_zero_of_abs_lt
        (R := R) (k := K0 ω) hinitial)
  have hpotential : (R : ℝ) =
      F (currentOfCounts K0 Nplus Nminus u ω) - F (K0 ω) := by
    rw [hterminal, hinitialPotential]
    ring
  have hunmasked : (R : ℝ) ≤
      countingIntegral Nplus
          (fun s ω' ↦ positiveOutwardBand R
            (leftCurrentOfCounts K0 Nplus Nminus s ω')) u ω +
        countingIntegral Nminus
          (fun s ω' ↦ negativeOutwardBand R
            (leftCurrentOfCounts K0 Nplus Nminus s ω')) u ω := by
    rw [hpotential, hchain]
    exact add_le_add hplusStep hminusStep
  have hplusStop := countingIntegral_le_throughStop_of_le
    (fun ω' ↦ hplus.monotone ω')
    (fun s ω' ↦ by
      unfold positiveOutwardBand
      split_ifs <;> norm_num) τ huT huτ
    (H := fun s ω' ↦ positiveOutwardBand R
      (leftCurrentOfCounts K0 Nplus Nminus s ω'))
  have hminusStop := countingIntegral_le_throughStop_of_le
    (fun ω' ↦ hminus.monotone ω')
    (fun s ω' ↦ by
      unfold negativeOutwardBand
      split_ifs <;> norm_num) τ huT huτ
    (H := fun s ω' ↦ negativeOutwardBand R
      (leftCurrentOfCounts K0 Nplus Nminus s ω'))
  change (R : ℝ) ≤
    countingIntegral Nplus
        (fun s ω' ↦ throughStopMask τ s ω' *
          positiveOutwardBand R (leftCurrentOfCounts K0 Nplus Nminus s ω')) T ω +
      countingIntegral Nminus
        (fun s ω' ↦ throughStopMask τ s ω' *
          negativeOutwardBand R (leftCurrentOfCounts K0 Nplus Nminus s ω')) T ω
  exact hunmasked.trans (add_le_add hplusStop hminusStop)

/-! ## Compensator expectation and the quadratic band bound -/

/-- A bounded simple predictable counting integral is integrable whenever its unit compensator
is integrable. -/
theorem countingIntegral_integrable_of_intensity
    {μ : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    [SigmaFiniteFiltration μ ℱ]
    {N : ℝ≥0 → Ω → ℕ} {Λ H : ℝ≥0 → Ω → ℝ}
    (hΛ : HasPredictableIntensity μ ℱ N Λ)
    (hH : IsBoundedSimplePredictable ℱ H)
    (hA : ∀ t, Integrable
      (fun ω ↦ integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) t ω) μ)
    (t : ℝ≥0) :
    Integrable (countingIntegral N H t) μ := by
  have hComp := hΛ.compensatedIntegral_integrable hH t
  have hIntensity := integratedIntensity_integrable_of_boundedPredictable
    hΛ hH.isBoundedPredictable hA t
  have heq : countingIntegral N H t = fun ω ↦
      compensatedIntegral N Λ H t ω + integratedIntensity Λ H t ω := by
    funext ω
    simp only [compensatedIntegral]
    ring
  rw [heq]
  exact hComp.add hIntensity

/-- The expectation of a bounded simple predictable counting integral equals the expectation of
its genuine compensator. -/
theorem integral_countingIntegral_eq_integratedIntensity
    {μ : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    [SigmaFiniteFiltration μ ℱ]
    {N : ℝ≥0 → Ω → ℕ} {Λ H : ℝ≥0 → Ω → ℝ}
    (hN : IsSimpleCountingProcess ℱ N)
    (hΛ : HasPredictableIntensity μ ℱ N Λ)
    (hH : IsBoundedSimplePredictable ℱ H)
    (hA : ∀ t, Integrable
      (fun ω ↦ integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) t ω) μ)
    (t : ℝ≥0) :
    ∫ ω, countingIntegral N H t ω ∂μ =
      ∫ ω, integratedIntensity Λ H t ω ∂μ := by
  have hM := hΛ.martingale hH
  have hzero : ∫ ω, compensatedIntegral N Λ H t ω ∂μ = 0 := by
    have hzeroProcess : compensatedIntegral N Λ H 0 = 0 := by
      funext ω
      simp [compensatedIntegral, countingIntegral, integratedIntensity, hN.zero]
    have hEq := hM.setIntegral_eq (i := 0) (j := t) bot_le
      (s := Set.univ) MeasurableSet.univ
    rw [Measure.restrict_univ, hzeroProcess] at hEq
    simpa only [Pi.zero_apply, integral_zero] using hEq.symm
  have hCount := countingIntegral_integrable_of_intensity hΛ hH hA t
  have hIntensity := integratedIntensity_integrable_of_boundedPredictable
    hΛ hH.isBoundedPredictable hA t
  change (∫ ω, countingIntegral N H t ω - integratedIntensity Λ H t ω ∂μ) = 0
    at hzero
  rw [integral_sub hCount hIntensity] at hzero
  linarith

omit [MeasurableSpace Ω] in
private theorem timeMeasure_singleton_zero_currentExcursion (a : ℝ≥0) :
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
      have hxcoe : Real.toNNReal x = Real.toNNReal (a : ℝ) := by
        simpa using hxa
      exact Real.toNNReal_eq_toNNReal_iff hx0 a.2 |>.mp hxcoe
    · intro hxa
      subst x
      exact ⟨Real.toNNReal_coe, a.2⟩
  rw [hpre, Real.volume_singleton]

omit [MeasurableSpace Ω] in
/-- A deterministic stopping coordinate is different from Lebesgue-a.e. time point. -/
theorem ae_coe_ne_stoppingCoordinate
    (τ : Ω → WithTop ℝ≥0) (T : ℝ≥0) (ω : Ω) :
    ∀ᵐ (s : ℝ≥0) ∂(timeMeasure.restrict (Ioc (0 : ℝ≥0) T)),
      (s : WithTop ℝ≥0) ≠ τ ω := by
  cases hτ : τ ω with
  | top =>
      filter_upwards with s
      exact WithTop.coe_ne_top
  | coe a =>
      have hne : ∀ᵐ (s : ℝ≥0) ∂timeMeasure, s ≠ a := by
        apply MeasureTheory.ae_iff.mpr
        simpa only [not_ne_iff, Set.ofPred_eq_eq_singleton] using
          timeMeasure_singleton_zero_currentExcursion a
      filter_upwards [ae_restrict_of_ae hne] with s hs
      simpa only [hτ, ne_eq, WithTop.coe_eq_coe] using hs

omit [MeasurableSpace Ω] in
/-- At one integer state the positive and negative outward bands are disjoint.  Under a common
rate cap `C`, their combined instantaneous outward rate is bounded by `C * k² / R²`. -/
theorem outwardBandRate_le_quadratic
    {R : ℕ} (hR : 0 < R) {C ratePlus rateMinus : ℝ}
    (hC : 0 ≤ C) (hplus : ratePlus ≤ C)
    (hminus : rateMinus ≤ C) (k : ℤ) :
    positiveOutwardBand R k * ratePlus + negativeOutwardBand R k * rateMinus ≤
      C * (k : ℝ) ^ 2 / (R : ℝ) ^ 2 := by
  have hRreal : 0 < (R : ℝ) := by exact_mod_cast hR
  apply (le_div_iff₀ (sq_pos_of_pos hRreal)).2
  by_cases hp : (R : ℤ) ≤ k ∧ k < 2 * (R : ℤ)
  · have hm : ¬(-(2 * (R : ℤ)) < k ∧ k ≤ -(R : ℤ)) := by
      omega
    rw [show positiveOutwardBand R k = 1 by simp [positiveOutwardBand, hp],
      show negativeOutwardBand R k = 0 by simp [negativeOutwardBand, hm]]
    norm_num
    have hk : (R : ℝ) ≤ (k : ℝ) := by exact_mod_cast hp.1
    have hsq : (R : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 := by nlinarith
    calc
      ratePlus * (R : ℝ) ^ 2 ≤ C * (R : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hplus (sq_nonneg _)
      _ ≤ C * (k : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hsq hC
  · by_cases hm : -(2 * (R : ℤ)) < k ∧ k ≤ -(R : ℤ)
    · rw [show positiveOutwardBand R k = 0 by simp [positiveOutwardBand, hp],
        show negativeOutwardBand R k = 1 by simp [negativeOutwardBand, hm]]
      norm_num
      have hk : (k : ℝ) ≤ -(R : ℝ) := by exact_mod_cast hm.2
      have hsq : (R : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 := by nlinarith
      calc
        rateMinus * (R : ℝ) ^ 2 ≤ C * (R : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hminus (sq_nonneg _)
        _ ≤ C * (k : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hsq hC
    · rw [show positiveOutwardBand R k = 0 by simp [positiveOutwardBand, hp],
        show negativeOutwardBand R k = 0 by simp [negativeOutwardBand, hm]]
      norm_num
      exact mul_nonneg hC (sq_nonneg _)

/-- The genuine compensators of the two outward-band counts are controlled by the stopped
quadratic occupation.  Since the positive and negative bands are disjoint, the common rate cap
appears once rather than twice. -/
theorem integral_throughStopOutwardBandCount_le
    {μ : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    [SigmaFiniteFiltration μ ℱ]
    {K0 : Ω → ℤ} {Nplus Nminus : ℝ≥0 → Ω → ℕ}
    {Λplus Λminus : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}
    (hplus : IsSimpleCountingProcess ℱ Nplus)
    (hminus : IsSimpleCountingProcess ℱ Nminus)
    (hΛplus : HasPredictableIntensity μ ℱ Nplus Λplus)
    (hΛminus : HasPredictableIntensity μ ℱ Nminus Λminus)
    (hK0 : StronglyMeasurable[ℱ 0] (fun ω ↦ (K0 ω : ℝ)))
    (hMask : IsBoundedSimplePredictable ℱ (throughStopMask τ))
    (hAplus : ∀ t, Integrable
      (fun ω ↦ integratedIntensity Λplus (fun _ _ ↦ (1 : ℝ)) t ω) μ)
    (hAminus : ∀ t, Integrable
      (fun ω ↦ integratedIntensity Λminus (fun _ _ ↦ (1 : ℝ)) t ω) μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hRate : ∀ ω (s : ℝ≥0), (s : WithTop ℝ≥0) < τ ω →
      Λplus s ω ≤ C ∧ Λminus s ω ≤ C)
    {R : ℕ} (hR : 0 < R) (T : ℝ≥0)
    (hOccupation : Integrable
      (throughStopClippedQuadraticOccupation τ K0 Nplus Nminus T) μ)
    (hOccupationTime : ∀ ω, IntegrableOn
      (fun s ↦ throughStopMask τ s ω *
        (leftCurrentOfCounts K0 Nplus Nminus s ω : ℝ) ^ 2)
      (Ioc (0 : ℝ≥0) T) timeMeasure) :
    ∫ ω, throughStopOutwardBandCount τ R K0 Nplus Nminus T ω ∂μ ≤
      C * (∫ ω, throughStopClippedQuadraticOccupation
        τ K0 Nplus Nminus T ω ∂μ) / (R : ℝ) ^ 2 := by
  let Hplus := positiveOutwardBandIntegrand τ R K0 Nplus Nminus
  let Hminus := negativeOutwardBandIntegrand τ R K0 Nplus Nminus
  have hHplus : IsBoundedSimplePredictable ℱ Hplus := by
    simpa only [Hplus] using
      positiveOutwardBandIntegrand_boundedSimplePredictable
        hplus hminus hK0 hMask R
  have hHminus : IsBoundedSimplePredictable ℱ Hminus := by
    simpa only [Hminus] using
      negativeOutwardBandIntegrand_boundedSimplePredictable
        hplus hminus hK0 hMask R
  have hCountPlus : Integrable (countingIntegral Nplus Hplus T) μ :=
    countingIntegral_integrable_of_intensity hΛplus hHplus hAplus T
  have hCountMinus : Integrable (countingIntegral Nminus Hminus T) μ :=
    countingIntegral_integrable_of_intensity hΛminus hHminus hAminus T
  have hIntensityPlus : Integrable
      (fun ω ↦ integratedIntensity Λplus Hplus T ω) μ :=
    integratedIntensity_integrable_of_boundedPredictable
      hΛplus hHplus.isBoundedPredictable hAplus T
  have hIntensityMinus : Integrable
      (fun ω ↦ integratedIntensity Λminus Hminus T ω) μ :=
    integratedIntensity_integrable_of_boundedPredictable
      hΛminus hHminus.isBoundedPredictable hAminus T
  have hplusTime : ∀ ω, IntegrableOn
      (fun s ↦ Hplus s ω * Λplus s ω)
      (Ioc (0 : ℝ≥0) T) timeMeasure := fun ω ↦
    hHplus.isBoundedPredictable.integrableOn_mul_intensity hΛplus T ω
  have hminusTime : ∀ ω, IntegrableOn
      (fun s ↦ Hminus s ω * Λminus s ω)
      (Ioc (0 : ℝ≥0) T) timeMeasure := fun ω ↦
    hHminus.isBoundedPredictable.integrableOn_mul_intensity hΛminus T ω
  have hpath : ∀ ω,
      integratedIntensity Λplus Hplus T ω + integratedIntensity Λminus Hminus T ω ≤
        (C / (R : ℝ) ^ 2) *
          throughStopClippedQuadraticOccupation τ K0 Nplus Nminus T ω := by
    intro ω
    have hendpoint := ae_coe_ne_stoppingCoordinate τ T ω
    have hpoint : ∀ᵐ (s : ℝ≥0)
        ∂(timeMeasure.restrict (Ioc (0 : ℝ≥0) T)),
        Hplus s ω * Λplus s ω + Hminus s ω * Λminus s ω ≤
          (C / (R : ℝ) ^ 2) *
            (throughStopMask τ s ω *
              (leftCurrentOfCounts K0 Nplus Nminus s ω : ℝ) ^ 2) := by
      filter_upwards [hendpoint] with s hsne
      by_cases hsle : (s : WithTop ℝ≥0) ≤ τ ω
      · have hslt : (s : WithTop ℝ≥0) < τ ω := lt_of_le_of_ne hsle hsne
        have hrates := hRate ω s hslt
        have hband := outwardBandRate_le_quadratic hR hC hrates.1 hrates.2
          (leftCurrentOfCounts K0 Nplus Nminus s ω)
        dsimp only [Hplus, Hminus, positiveOutwardBandIntegrand,
          negativeOutwardBandIntegrand]
        simp only [throughStopMask, ite_eq_left hsle, one_mul]
        convert hband using 1
        all_goals ring
      · dsimp only [Hplus, Hminus, positiveOutwardBandIntegrand,
          negativeOutwardBandIntegrand]
        simp only [throughStopMask, ite_eq_right hsle, zero_mul]
        norm_num
    have hleftInt : IntegrableOn
        (fun s ↦ Hplus s ω * Λplus s ω + Hminus s ω * Λminus s ω)
        (Ioc (0 : ℝ≥0) T) timeMeasure :=
      (hplusTime ω).add (hminusTime ω)
    have hrightInt : IntegrableOn
        (fun s ↦ (C / (R : ℝ) ^ 2) *
          (throughStopMask τ s ω *
            (leftCurrentOfCounts K0 Nplus Nminus s ω : ℝ) ^ 2))
        (Ioc (0 : ℝ≥0) T) timeMeasure :=
      (hOccupationTime ω).const_mul _
    have hmono := integral_mono_ae hleftInt hrightInt hpoint
    rw [integratedIntensity, integratedIntensity,
      ← integral_add (hplusTime ω) (hminusTime ω)]
    rw [throughStopClippedQuadraticOccupation, ← integral_const_mul]
    exact hmono
  have hIntensityBound :
      (∫ ω, integratedIntensity Λplus Hplus T ω +
          integratedIntensity Λminus Hminus T ω ∂μ) ≤
        C * (∫ ω, throughStopClippedQuadraticOccupation
          τ K0 Nplus Nminus T ω ∂μ) / (R : ℝ) ^ 2 := by
    have hmono := integral_mono_ae (hIntensityPlus.add hIntensityMinus)
      (hOccupation.const_mul (C / (R : ℝ) ^ 2)) (ae_of_all _ hpath)
    rw [integral_const_mul] at hmono
    calc
      (∫ ω, integratedIntensity Λplus Hplus T ω +
          integratedIntensity Λminus Hminus T ω ∂μ) ≤
          (C / (R : ℝ) ^ 2) *
            ∫ ω, throughStopClippedQuadraticOccupation
              τ K0 Nplus Nminus T ω ∂μ := hmono
      _ = C * (∫ ω, throughStopClippedQuadraticOccupation
          τ K0 Nplus Nminus T ω ∂μ) / (R : ℝ) ^ 2 := by ring
  rw [integral_add hIntensityPlus hIntensityMinus] at hIntensityBound
  change (∫ ω, countingIntegral Nplus Hplus T ω +
      countingIntegral Nminus Hminus T ω ∂μ) ≤ _
  rw [integral_add hCountPlus hCountMinus,
    integral_countingIntegral_eq_integratedIntensity
      hplus hΛplus hHplus hAplus T,
    integral_countingIntegral_eq_integratedIntensity
      hminus hΛminus hHminus hAminus T]
  exact hIntensityBound

/-! ## A measurable excursion hull and its cubic tail -/

/-- The raw event that the stopped post-jump current reaches radius `2 * R` by time `T`.
No measurability is asserted for the uncountable existential quantifier over time. -/
def throughStopCurrentExcursionRaw
    (τ : Ω → WithTop ℝ≥0) (R : ℕ) (K0 : Ω → ℤ)
    (Nplus Nminus : ℝ≥0 → Ω → ℕ) (T : ℝ≥0) : Set Ω :=
  {ω | ∃ u : ℝ≥0, u ≤ T ∧ (u : WithTop ℝ≥0) ≤ τ ω ∧
    2 * (R : ℝ) ≤ |(currentOfCounts K0 Nplus Nminus u ω : ℝ)|}

/-- Measurable hull of the raw stopped-current excursion event. -/
def throughStopCurrentExcursionEvent
    (μ : Measure Ω) (τ : Ω → WithTop ℝ≥0) (R : ℕ) (K0 : Ω → ℤ)
    (Nplus Nminus : ℝ≥0 → Ω → ℕ) (T : ℝ≥0) : Set Ω :=
  toMeasurable μ
    (throughStopCurrentExcursionRaw τ R K0 Nplus Nminus T)

theorem measurableSet_throughStopCurrentExcursionEvent
    (μ : Measure Ω) (τ : Ω → WithTop ℝ≥0) (R : ℕ) (K0 : Ω → ℤ)
    (Nplus Nminus : ℝ≥0 → Ω → ℕ) (T : ℝ≥0) :
    MeasurableSet
      (throughStopCurrentExcursionEvent μ τ R K0 Nplus Nminus T) := by
  exact measurableSet_toMeasurable _ _

theorem throughStopCurrentExcursionRaw_subset_event
    (μ : Measure Ω) (τ : Ω → WithTop ℝ≥0) (R : ℕ) (K0 : Ω → ℤ)
    (Nplus Nminus : ℝ≥0 → Ω → ℕ) (T : ℝ≥0) :
    throughStopCurrentExcursionRaw τ R K0 Nplus Nminus T ⊆
      throughStopCurrentExcursionEvent μ τ R K0 Nplus Nminus T := by
  exact subset_toMeasurable _ _

omit [MeasurableSpace Ω] in
theorem throughStopOutwardBandCount_nonneg
    (τ : Ω → WithTop ℝ≥0) (R : ℕ) (K0 : Ω → ℤ)
    (Nplus Nminus : ℝ≥0 → Ω → ℕ) (T : ℝ≥0) (ω : Ω) :
    0 ≤ throughStopOutwardBandCount τ R K0 Nplus Nminus T ω := by
  apply add_nonneg
  · unfold countingIntegral
    apply Finset.sum_nonneg
    intro k hk
    dsimp only [positiveOutwardBandIntegrand]
    unfold throughStopMask positiveOutwardBand
    split_ifs <;> norm_num
  · unfold countingIntegral
    apply Finset.sum_nonneg
    intro k hk
    dsimp only [negativeOutwardBandIntegrand]
    unfold throughStopMask negativeOutwardBand
    split_ifs <;> norm_num

theorem throughStopCurrentExcursionRaw_subset_initial_or_outwardCount
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {K0 : Ω → ℤ} {Nplus Nminus : ℝ≥0 → Ω → ℕ}
    (hplus : IsSimpleCountingProcess ℱ Nplus)
    (hminus : IsSimpleCountingProcess ℱ Nminus)
    (hNo : ∀ u, NoSimultaneousJumpsOn Nplus Nminus u)
    {τ : Ω → WithTop ℝ≥0} {R : ℕ} {T : ℝ≥0} :
    throughStopCurrentExcursionRaw τ R K0 Nplus Nminus T ⊆
      {ω | (R : ℝ) ≤ |(K0 ω : ℝ)|} ∪
        {ω | (R : ℝ) ≤
          throughStopOutwardBandCount τ R K0 Nplus Nminus T ω} := by
  intro ω hω
  rcases hω with ⟨u, huT, huτ, hreaches⟩
  by_cases hinitial : (R : ℝ) ≤ |(K0 ω : ℝ)|
  · exact Or.inl hinitial
  · apply Or.inr
    exact radius_le_throughStopOutwardBandCount_of_reaches
      hplus hminus (hNo u) huT huτ (lt_of_not_ge hinitial) hreaches

/-- A stopped nearest-neighbour current has a cubic excursion tail.  The two outward bands are
disjoint, so the common rate cap `C` occurs only once in the occupation term.  The probability
is stated for the measurable hull of the raw time-existential event. -/
theorem measureReal_throughStopCurrentExcursionEvent_le
    {μ : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ ℱ]
    {K0 : Ω → ℤ} {Nplus Nminus : ℝ≥0 → Ω → ℕ}
    {Λplus Λminus : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}
    (hplus : IsSimpleCountingProcess ℱ Nplus)
    (hminus : IsSimpleCountingProcess ℱ Nminus)
    (hNo : ∀ u, NoSimultaneousJumpsOn Nplus Nminus u)
    (hΛplus : HasPredictableIntensity μ ℱ Nplus Λplus)
    (hΛminus : HasPredictableIntensity μ ℱ Nminus Λminus)
    (hK0 : StronglyMeasurable[ℱ 0] (fun ω ↦ (K0 ω : ℝ)))
    (hMask : IsBoundedSimplePredictable ℱ (throughStopMask τ))
    (hAplus : ∀ t, Integrable
      (fun ω ↦ integratedIntensity Λplus (fun _ _ ↦ (1 : ℝ)) t ω) μ)
    (hAminus : ∀ t, Integrable
      (fun ω ↦ integratedIntensity Λminus (fun _ _ ↦ (1 : ℝ)) t ω) μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hRate : ∀ ω (s : ℝ≥0), (s : WithTop ℝ≥0) < τ ω →
      Λplus s ω ≤ C ∧ Λminus s ω ≤ C)
    {R : ℕ} (hR : 0 < R) (T : ℝ≥0)
    (hInitialMoment : Integrable (fun ω ↦ |(K0 ω : ℝ)| ^ 3) μ)
    (hOccupation : Integrable
      (throughStopClippedQuadraticOccupation τ K0 Nplus Nminus T) μ)
    (hOccupationTime : ∀ ω, IntegrableOn
      (fun s ↦ throughStopMask τ s ω *
        (leftCurrentOfCounts K0 Nplus Nminus s ω : ℝ) ^ 2)
      (Ioc (0 : ℝ≥0) T) timeMeasure) :
    μ.real (throughStopCurrentExcursionEvent
      μ τ R K0 Nplus Nminus T) ≤
      (∫ ω, |(K0 ω : ℝ)| ^ 3 ∂μ) / (R : ℝ) ^ 3 +
        C * (∫ ω, throughStopClippedQuadraticOccupation
          τ K0 Nplus Nminus T ω ∂μ) / (R : ℝ) ^ 3 := by
  let Hplus := positiveOutwardBandIntegrand τ R K0 Nplus Nminus
  let Hminus := negativeOutwardBandIntegrand τ R K0 Nplus Nminus
  let J := throughStopOutwardBandCount τ R K0 Nplus Nminus T
  have hRreal : 0 < (R : ℝ) := by exact_mod_cast hR
  have hHplus : IsBoundedSimplePredictable ℱ Hplus := by
    simpa only [Hplus] using
      positiveOutwardBandIntegrand_boundedSimplePredictable
        hplus hminus hK0 hMask R
  have hHminus : IsBoundedSimplePredictable ℱ Hminus := by
    simpa only [Hminus] using
      negativeOutwardBandIntegrand_boundedSimplePredictable
        hplus hminus hK0 hMask R
  have hJIntegrable : Integrable J μ := by
    have hplusInt := countingIntegral_integrable_of_intensity
      hΛplus hHplus hAplus T
    have hminusInt := countingIntegral_integrable_of_intensity
      hΛminus hHminus hAminus T
    change Integrable (fun ω ↦ countingIntegral Nplus Hplus T ω +
      countingIntegral Nminus Hminus T ω) μ
    exact hplusInt.add hminusInt
  have hJnonneg : ∀ ω, 0 ≤ J ω := by
    intro ω
    exact throughStopOutwardBandCount_nonneg τ R K0 Nplus Nminus T ω
  have hJExpectation : ∫ ω, J ω ∂μ ≤
      C * (∫ ω, throughStopClippedQuadraticOccupation
        τ K0 Nplus Nminus T ω ∂μ) / (R : ℝ) ^ 2 := by
    simpa only [J] using integral_throughStopOutwardBandCount_le
      hplus hminus hΛplus hΛminus hK0 hMask hAplus hAminus
      hC hRate hR T hOccupation hOccupationTime
  have hinitialSet :
      {ω | (R : ℝ) ≤ |(K0 ω : ℝ)|} =
        {ω | (R : ℝ) ^ 3 ≤ |(K0 ω : ℝ)| ^ 3} := by
    ext ω
    exact (pow_le_pow_iff_left₀ hRreal.le (abs_nonneg _) (by norm_num : 3 ≠ 0)).symm
  have hinitialMarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (f := fun ω ↦ |(K0 ω : ℝ)| ^ 3)
    (ae_of_all _ fun ω ↦ pow_nonneg (abs_nonneg _) 3)
    hInitialMoment ((R : ℝ) ^ 3)
  have hinitialTail : μ.real {ω | (R : ℝ) ≤ |(K0 ω : ℝ)|} ≤
      (∫ ω, |(K0 ω : ℝ)| ^ 3 ∂μ) / (R : ℝ) ^ 3 := by
    rw [hinitialSet, le_div_iff₀ (pow_pos hRreal 3)]
    simpa only [mul_comm] using hinitialMarkov
  have hJMarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (f := J) (ae_of_all _ hJnonneg) hJIntegrable (R : ℝ)
  have hJTail : μ.real {ω | (R : ℝ) ≤ J ω} ≤
      C * (∫ ω, throughStopClippedQuadraticOccupation
        τ K0 Nplus Nminus T ω ∂μ) / (R : ℝ) ^ 3 := by
    calc
      μ.real {ω | (R : ℝ) ≤ J ω} ≤ (∫ ω, J ω ∂μ) / (R : ℝ) := by
        rw [le_div_iff₀ hRreal]
        simpa only [mul_comm] using hJMarkov
      _ ≤ (C * (∫ ω, throughStopClippedQuadraticOccupation
          τ K0 Nplus Nminus T ω ∂μ) / (R : ℝ) ^ 2) / (R : ℝ) :=
        div_le_div_of_nonneg_right hJExpectation hRreal.le
      _ = C * (∫ ω, throughStopClippedQuadraticOccupation
          τ K0 Nplus Nminus T ω ∂μ) / (R : ℝ) ^ 3 := by ring
  have hrawSubset :=
    throughStopCurrentExcursionRaw_subset_initial_or_outwardCount
      hplus hminus hNo (K0 := K0) (τ := τ) (R := R) (T := T)
  calc
    μ.real (throughStopCurrentExcursionEvent μ τ R K0 Nplus Nminus T) =
        μ.real (throughStopCurrentExcursionRaw τ R K0 Nplus Nminus T) := by
      simp only [throughStopCurrentExcursionEvent, Measure.real,
        measure_toMeasurable]
    _ ≤ μ.real ({ω | (R : ℝ) ≤ |(K0 ω : ℝ)|} ∪
          {ω | (R : ℝ) ≤ J ω}) := by
      exact measureReal_mono hrawSubset
    _ ≤ μ.real {ω | (R : ℝ) ≤ |(K0 ω : ℝ)|} +
          μ.real {ω | (R : ℝ) ≤ J ω} := measureReal_union_le _ _
    _ ≤ (∫ ω, |(K0 ω : ℝ)| ^ 3 ∂μ) / (R : ℝ) ^ 3 +
          C * (∫ ω, throughStopClippedQuadraticOccupation
            τ K0 Nplus Nminus T ω ∂μ) / (R : ℝ) ^ 3 :=
      add_le_add hinitialTail hJTail

end OTSelector.CountingProcess
