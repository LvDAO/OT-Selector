import OTSelector.Feedback.FeedbackSpatialMartingale
import OTSelector.Limit.FeedbackMartingaleProblemStoppedProcess

/-!
# Quadratic count identities for the actual stopped feedback windows

The square transform uses the existing predictable-intensity interface. Its finite range comes
from the original finite number of labels, so no exponential-martingale construction is needed.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Classical NNReal Topology

namespace OTSelector.CountingProcess

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The elementary square chain rule for a simple counting path. -/
theorem countingIntegral_countBefore_twice_add_one
    {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {N : ℝ≥0 → Ω → ℕ}
    (hN : IsSimpleCountingProcess F N) (t : ℝ≥0) (ω : Ω) :
    countingIntegral N (fun s ω ↦ 2 * (countBefore N s ω : ℝ) + 1) t ω =
      (N t ω : ℝ) ^ 2 := by
  unfold countingIntegral
  have heq : (∑ k ∈ Finset.range (N t ω),
      (2 * (countBefore N (jumpTime N k ω) ω : ℝ) + 1)) =
        ∑ k ∈ Finset.range (N t ω), (2 * (k : ℝ) + 1) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [countBefore_jumpTime (hN.monotone ω) (hN.rightContinuous ω)
      (hN.jumpTime_injOn ω t) (Finset.mem_range.mp hk)]
  rw [heq]
  have hs (m : ℕ) : (∑ k ∈ Finset.range m, (2 * (k : ℝ) + 1)) = (m : ℝ)^2 := by
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  exact hs _

/-- Finite population makes the square chain-rule integrand bounded and finite-valued. -/
theorem countBefore_twice_add_one_boundedSimplePredictable
    {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {N : ℝ≥0 → Ω → ℕ}
    (hN : IsSimpleCountingProcess F N) {m : ℕ} (hNm : ∀ t ω, N t ω ≤ m) :
    IsBoundedSimplePredictable F (fun s ω ↦ 2 * (countBefore N s ω : ℝ) + 1) := by
  have hb (t : ℝ≥0) (ω : Ω) : countBefore N t ω ≤ m :=
    (hN.countBefore_le_at t ω).trans (hNm t ω)
  refine ⟨(stronglyMeasurable_const.mul (stronglyMeasurable_countBefore
    hN.stronglyAdapted hN.monotone)).add stronglyMeasurable_const, ?_,
      2 * (m : ℝ) + 1, by positivity, ?_⟩
  · apply ((Finset.finite_toSet (Finset.range (m + 1))).image
      (fun k : ℕ ↦ 2 * (k : ℝ) + 1)).subset
    rintro _ ⟨⟨t, ω⟩, rfl⟩
    exact ⟨countBefore N t ω, by simpa using Nat.lt_succ_of_le (hb t ω), rfl⟩
  · intro t ω
    rw [abs_of_nonneg (by positivity)]
    have hh : (countBefore N t ω : ℝ) ≤ (m : ℝ) := by exact_mod_cast hb t ω
    dsimp only
    linarith

/-- The stopped count square has its genuine predictable compensator. -/
theorem stoppedCount_square_compensated_martingale
    {μ : Measure Ω} {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {N : ℝ≥0 → Ω → ℕ} {Λ : ℝ≥0 → Ω → ℝ}
    (hN : IsSimpleCountingProcess F N) (hΛ : HasPredictableIntensity μ F N Λ)
    {m : ℕ} (hNm : ∀ t ω, N t ω ≤ m)
    {τ : Ω → WithTop ℝ≥0} (hmask : IsBoundedSimplePredictable F (throughStopMask τ)) :
    Martingale (fun t ω ↦
      (stoppedProcess (fun u ω ↦ (N u ω : ℝ)) τ t ω)^2 -
        integratedIntensity Λ (fun u ω ↦
          throughStopMask τ u ω * (2 * (countBefore N u ω : ℝ) + 1)) t ω) F μ := by
  have h := hΛ.martingale (hmask.mul_process
    (countBefore_twice_add_one_boundedSimplePredictable hN hNm))
  convert h using 1
  funext t ω
  unfold compensatedIntegral
  rw [countingIntegral_mul_throughStopMask hN.monotone hN.rightContinuous,
    countingIntegral_countBefore_twice_add_one hN]
  rfl

/-- The first stopped count transform, using the same genuine intensity. -/
theorem stoppedCount_compensated_martingale
    {μ : Measure Ω} {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {N : ℝ≥0 → Ω → ℕ} {Λ : ℝ≥0 → Ω → ℝ}
    (hN : IsSimpleCountingProcess F N) (hΛ : HasPredictableIntensity μ F N Λ)
    {τ : Ω → WithTop ℝ≥0} (hmask : IsBoundedSimplePredictable F (throughStopMask τ)) :
    Martingale (fun t ω ↦ stoppedProcess (fun u ω ↦ (N u ω : ℝ)) τ t ω -
      integratedIntensity Λ (throughStopMask τ) t ω) F μ := by
  have h := hΛ.martingale hmask
  convert h using 1
  funext t ω
  unfold compensatedIntegral
  have heq : countingIntegral N (throughStopMask τ) t ω =
      countingIntegral N (fun _ _ ↦ (1 : ℝ))
        ((min (t : WithTop ℝ≥0) (τ ω)).untopA) ω := by
    convert countingIntegral_mul_throughStopMask hN.monotone
      hN.rightContinuous τ (fun _ _ ↦ (1 : ℝ)) t ω using 1 <;> first | rfl | simp only [mul_one]
  rw [heq]
  simp only [countingIntegral, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rfl


/-- First and second count compensators imply a local second-moment estimate. The two pathwise
bounds below are the ordinary integral bounds supplied by the localized physical rate. -/
theorem integral_sq_count_increment_le_of_compensators
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {Q A D : ℝ≥0 → Ω → ℝ} (hQ : StronglyAdapted F Q)
    {m : ℝ} (hbound : ∀ u ω, ‖Q u ω‖ ≤ m)
    (hM : Martingale (fun u ω ↦ Q u ω - A u ω) F μ)
    (hM2 : Martingale (fun u ω ↦ Q u ω ^ 2 - D u ω) F μ)
    {s t : ℝ≥0} (hst : s ≤ t) {K : ℝ} (hK : 0 ≤ K)
    (hA : ∀ ω, A t ω - A s ω ≤ K)
    (hD : ∀ ω, D t ω - D s ω - 2 * Q s ω * (A t ω - A s ω) ≤
      (2 * (Q t ω - Q s ω) + 1) * K) :
    (∫ ω, (Q t ω - Q s ω)^2 ∂μ) ≤ K + 2 * K^2 := by
  have hiQ (u : ℝ≥0) : Integrable (Q u) μ :=
    Integrable.of_bound ((hQ u).mono (F.le u)).aestronglyMeasurable m
      (Eventually.of_forall (hbound u))
  have hiQ2 (u : ℝ≥0) : Integrable (fun ω ↦ Q u ω ^ 2) μ := by
    apply Integrable.of_bound (((hQ u).mono (F.le u)).pow 2).aestronglyMeasurable (m^2)
    filter_upwards with ω
    simp only [Pi.pow_apply, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hbound u ω) 2
  have hiA (u : ℝ≥0) : Integrable (A u) μ := by
    convert (hiQ u).sub (hM.integrable u) using 1
    funext ω; dsimp; ring
  have hiD (u : ℝ≥0) : Integrable (D u) μ := by
    convert (hiQ2 u).sub (hM2.integrable u) using 1
    funext ω; dsimp; ring
  let X : Ω → ℝ := fun ω ↦ Q t ω - Q s ω
  let Y : Ω → ℝ := fun ω ↦ A t ω - A s ω
  let Z : Ω → ℝ := fun ω ↦ D t ω - D s ω
  have hiX : Integrable X μ := (hiQ t).sub (hiQ s)
  have hiY : Integrable Y μ := (hiA t).sub (hiA s)
  have hiZ : Integrable Z μ := (hiD t).sub (hiD s)
  have hiXY : Integrable (fun ω ↦ Q s ω * (X ω - Y ω)) μ :=
    (hiX.sub hiY).bdd_mul ((hQ s).mono (F.le s)).aestronglyMeasurable
      (Eventually.of_forall (hbound s))
  have hiQY : Integrable (fun ω ↦ 2 * Q s ω * Y ω) μ := by
    convert (hiY.bdd_mul ((hQ s).mono (F.le s)).aestronglyMeasurable
      (Eventually.of_forall (hbound s))).const_mul 2 using 1
    funext ω; ring
  have hiX2 : Integrable (fun ω ↦ X ω ^ 2) μ := by
    apply Integrable.of_bound (hiX.aestronglyMeasurable.pow 2) ((2*m)^2)
    filter_upwards with ω
    simp only [Pi.pow_apply, norm_pow]
    apply pow_le_pow_left₀ (norm_nonneg _)
    exact (norm_sub_le _ _).trans (by linarith [hbound t ω, hbound s ω])
  have hzero : (∫ ω, X ω - Y ω ∂μ) = 0 := by
    have h := hM.setIntegral_eq hst (s := univ) MeasurableSet.univ
    simp only [Measure.restrict_univ] at h
    have hi := (hM.integrable t).sub (hM.integrable s)
    calc
      _ = ∫ ω, (Q t ω - A t ω) - (Q s ω - A s ω) ∂μ := by
        congr 1; funext ω; dsimp [X,Y]; ring
      _ = 0 := by rw [integral_sub (hM.integrable t) (hM.integrable s), h, sub_self]
  have hEX : (∫ ω, X ω ∂μ) ≤ K := by
    rw [integral_sub hiX hiY] at hzero
    have hEY : (∫ ω, Y ω ∂μ) ≤ K := by
      calc
        _ ≤ ∫ _ω : Ω, K ∂μ := integral_mono hiY (integrable_const K) hA
        _ = K := by simp
    linarith
  have hweight : (∫ ω, Q s ω * (X ω - Y ω) ∂μ) = 0 := by
    have hInt : Integrable (fun ω ↦ Q s ω *
      ((Q t ω - A t ω) - (Q s ω - A s ω))) μ := by
      convert hiXY using 1; funext ω; dsimp [X,Y]; ring
    have hz := Probability.integral_past_mul_martingale_increment_eq_zero hM hst (hQ s) hInt
    convert hz using 1; congr 1; funext ω; dsimp [X,Y]; ring
  have hzero2 : (∫ ω, (Q t ω ^ 2 - D t ω) - (Q s ω ^ 2 - D s ω) ∂μ) = 0 := by
    rw [integral_sub (hM2.integrable t) (hM2.integrable s)]
    have h := hM2.setIntegral_eq hst (s := univ) MeasurableSet.univ
    simp only [Measure.restrict_univ] at h
    rw [h, sub_self]
  have heq : (∫ ω, X ω^2 ∂μ) = ∫ ω, Z ω - 2 * Q s ω * Y ω ∂μ := by
    have halg : (fun ω ↦ X ω^2) = fun ω ↦
        (Z ω - 2 * Q s ω * Y ω) +
          ((Q t ω^2 - D t ω) - (Q s ω^2 - D s ω)) -
            2 * (Q s ω * (X ω - Y ω)) := by
      funext ω; dsimp [X,Y,Z]; ring
    rw [halg]
    rw [integral_sub (f := fun ω ↦ (Z ω - 2 * Q s ω * Y ω) +
      ((Q t ω^2 - D t ω) - (Q s ω^2 - D s ω)))
      ((hiZ.sub hiQY).add ((hM2.integrable t).sub (hM2.integrable s)))
      (hiXY.const_mul 2), integral_add (f := fun ω ↦ Z ω - 2 * Q s ω * Y ω)
        (g := fun ω ↦ (Q t ω^2 - D t ω) - (Q s ω^2 - D s ω))
        (hiZ.sub hiQY) ((hM2.integrable t).sub (hM2.integrable s)),
        integral_const_mul, hzero2, hweight]
    ring
  change (∫ ω, X ω^2 ∂μ) ≤ _
  rw [heq]
  calc
    _ ≤ ∫ ω, (2 * X ω + 1) * K ∂μ :=
      integral_mono (hiZ.sub hiQY) (((hiX.const_mul 2).add (integrable_const 1)).mul_const K) hD
    _ = (2 * (∫ ω, X ω ∂μ) + 1) * K := by
      rw [integral_mul_const, integral_add (hiX.const_mul 2) (integrable_const 1),
        integral_const_mul]; simp
    _ ≤ K + 2*K^2 := by nlinarith


theorem integral_factorial_count_increment_le_of_compensators
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {Q A D : ℝ≥0 → Ω → ℝ} (hQ : StronglyAdapted F Q)
    {m : ℝ} (hbound : ∀ u ω, ‖Q u ω‖ ≤ m)
    (hM : Martingale (fun u ω ↦ Q u ω - A u ω) F μ)
    (hM2 : Martingale (fun u ω ↦ Q u ω ^ 2 - D u ω) F μ)
    {s t : ℝ≥0} (hst : s ≤ t) {K : ℝ} (hK : 0 ≤ K)
    (hA : ∀ ω, A t ω - A s ω ≤ K)
    (hD : ∀ ω, D t ω - D s ω - 2 * Q s ω * (A t ω - A s ω) ≤
      2 * K * (Q t ω - Q s ω) + (A t ω - A s ω)) :
    (∫ ω, (Q t ω - Q s ω)^2 - (Q t ω - Q s ω) ∂μ) ≤ 2 * K^2 := by
  have hiQ (u : ℝ≥0) : Integrable (Q u) μ :=
    Integrable.of_bound ((hQ u).mono (F.le u)).aestronglyMeasurable m
      (Eventually.of_forall (hbound u))
  have hiQ2 (u : ℝ≥0) : Integrable (fun ω ↦ Q u ω ^ 2) μ := by
    apply Integrable.of_bound (((hQ u).mono (F.le u)).pow 2).aestronglyMeasurable (m^2)
    filter_upwards with ω
    simp only [Pi.pow_apply, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hbound u ω) 2
  have hiA (u : ℝ≥0) : Integrable (A u) μ := by
    convert (hiQ u).sub (hM.integrable u) using 1
    funext ω; dsimp; ring
  have hiD (u : ℝ≥0) : Integrable (D u) μ := by
    convert (hiQ2 u).sub (hM2.integrable u) using 1
    funext ω; dsimp; ring
  let X : Ω → ℝ := fun ω ↦ Q t ω - Q s ω
  let Y : Ω → ℝ := fun ω ↦ A t ω - A s ω
  let Z : Ω → ℝ := fun ω ↦ D t ω - D s ω
  have hiX : Integrable X μ := (hiQ t).sub (hiQ s)
  have hiY : Integrable Y μ := (hiA t).sub (hiA s)
  have hiZ : Integrable Z μ := (hiD t).sub (hiD s)
  have hiXY : Integrable (fun ω ↦ Q s ω * (X ω - Y ω)) μ :=
    (hiX.sub hiY).bdd_mul ((hQ s).mono (F.le s)).aestronglyMeasurable
      (Eventually.of_forall (hbound s))
  have hiQY : Integrable (fun ω ↦ 2 * Q s ω * Y ω) μ := by
    convert (hiY.bdd_mul ((hQ s).mono (F.le s)).aestronglyMeasurable
      (Eventually.of_forall (hbound s))).const_mul 2 using 1
    funext ω; ring
  have hiX2 : Integrable (fun ω ↦ X ω ^ 2) μ := by
    apply Integrable.of_bound (hiX.aestronglyMeasurable.pow 2) ((2*m)^2)
    filter_upwards with ω
    simp only [Pi.pow_apply, norm_pow]
    apply pow_le_pow_left₀ (norm_nonneg _)
    exact (norm_sub_le _ _).trans (by linarith [hbound t ω, hbound s ω])
  have hzero : (∫ ω, X ω - Y ω ∂μ) = 0 := by
    have h := hM.setIntegral_eq hst (s := univ) MeasurableSet.univ
    simp only [Measure.restrict_univ] at h
    have hi := (hM.integrable t).sub (hM.integrable s)
    calc
      _ = ∫ ω, (Q t ω - A t ω) - (Q s ω - A s ω) ∂μ := by
        congr 1; funext ω; dsimp [X,Y]; ring
      _ = 0 := by rw [integral_sub (hM.integrable t) (hM.integrable s), h, sub_self]
  have hEX : (∫ ω, X ω ∂μ) ≤ K := by
    rw [integral_sub hiX hiY] at hzero
    have hEY : (∫ ω, Y ω ∂μ) ≤ K := by
      calc
        _ ≤ ∫ _ω : Ω, K ∂μ := integral_mono hiY (integrable_const K) hA
        _ = K := by simp
    linarith
  have hweight : (∫ ω, Q s ω * (X ω - Y ω) ∂μ) = 0 := by
    have hInt : Integrable (fun ω ↦ Q s ω *
      ((Q t ω - A t ω) - (Q s ω - A s ω))) μ := by
      convert hiXY using 1; funext ω; dsimp [X,Y]; ring
    have hz := Probability.integral_past_mul_martingale_increment_eq_zero hM hst (hQ s) hInt
    convert hz using 1; congr 1; funext ω; dsimp [X,Y]; ring
  have hzero2 : (∫ ω, (Q t ω ^ 2 - D t ω) - (Q s ω ^ 2 - D s ω) ∂μ) = 0 := by
    rw [integral_sub (hM2.integrable t) (hM2.integrable s)]
    have h := hM2.setIntegral_eq hst (s := univ) MeasurableSet.univ
    simp only [Measure.restrict_univ] at h
    rw [h, sub_self]
  have heq : (∫ ω, X ω^2 ∂μ) = ∫ ω, Z ω - 2 * Q s ω * Y ω ∂μ := by
    have halg : (fun ω ↦ X ω^2) = fun ω ↦
        (Z ω - 2 * Q s ω * Y ω) +
          ((Q t ω^2 - D t ω) - (Q s ω^2 - D s ω)) -
            2 * (Q s ω * (X ω - Y ω)) := by
      funext ω; dsimp [X,Y,Z]; ring
    rw [halg]
    rw [integral_sub (f := fun ω ↦ (Z ω - 2 * Q s ω * Y ω) +
      ((Q t ω^2 - D t ω) - (Q s ω^2 - D s ω)))
      ((hiZ.sub hiQY).add ((hM2.integrable t).sub (hM2.integrable s)))
      (hiXY.const_mul 2), integral_add (f := fun ω ↦ Z ω - 2 * Q s ω * Y ω)
        (g := fun ω ↦ (Q t ω^2 - D t ω) - (Q s ω^2 - D s ω))
        (hiZ.sub hiQY) ((hM2.integrable t).sub (hM2.integrable s)),
        integral_const_mul, hzero2, hweight]
    ring
  change (∫ ω, X ω^2 - X ω ∂μ) ≤ _
  rw [integral_sub hiX2 hiX, heq]
  have hb : (∫ ω, Z ω - 2 * Q s ω * Y ω ∂μ) ≤
      2*K*(∫ ω, X ω ∂μ) + ∫ ω, Y ω ∂μ := by
    calc
      _ ≤ ∫ ω, 2*K*X ω + Y ω ∂μ :=
        integral_mono (hiZ.sub hiQY) ((hiX.const_mul _).add hiY) hD
      _ = _ := by rw [integral_add (hiX.const_mul _) hiY, integral_const_mul]
  rw [integral_sub hiX hiY] at hzero
  nlinarith

/-- A finite simple count of rate at most `C` before a stopping time has a uniform local
second moment. The factor `2` on the quadratic term avoids a stochastic Fubini argument. -/
theorem integral_sq_stoppedCount_increment_le
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {N : ℝ≥0 → Ω → ℕ} {Λ : ℝ≥0 → Ω → ℝ}
    (hN : IsSimpleCountingProcess F N) (hΛ : HasPredictableIntensity μ F N Λ)
    {m : ℕ} (hNm : ∀ u ω, N u ω ≤ m)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ)
    (hmask : IsBoundedSimplePredictable F (throughStopMask τ))
    {C : ℝ} (hC : 0 ≤ C) (hcap : ∀ (u : ℝ≥0) (ω : Ω), (u : WithTop ℝ≥0) < τ ω → Λ u ω ≤ C)
    {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ ω, (stoppedProcess (fun u ω ↦ (N u ω : ℝ)) τ t ω -
      stoppedProcess (fun u ω ↦ (N u ω : ℝ)) τ s ω)^2 ∂μ) ≤
        C * ((t : ℝ) - s) + 2 * (C * ((t : ℝ) - s))^2 := by
  let Q := stoppedProcess (fun u ω ↦ (N u ω : ℝ)) τ
  let A := integratedIntensity Λ (throughStopMask τ)
  let D := integratedIntensity Λ (fun u ω ↦
    throughStopMask τ u ω * (2 * (countBefore N u ω : ℝ) + 1))
  have hQ : StronglyAdapted F Q := by
    change StronglyAdapted F (stoppedProcess (fun u ω ↦ (N u ω : ℝ)) τ)
    rw [Limit.stoppedProcess_eq_cappedStoppingValue]
    exact Limit.stronglyAdapted_cappedStoppingValue_of_rightContinuous
      hN.stronglyAdapted hτ hN.rightContinuous
  have hQeq (u : ℝ≥0) (ω : Ω) : Q u ω = (N (cappedStoppingValue u τ ω) ω : ℝ) := by
    change stoppedProcess (fun u ω ↦ (N u ω : ℝ)) τ u ω = _
    rw [Limit.stoppedProcess_eq_cappedStoppingValue]
  have hQmono (ω : Ω) : Monotone (fun u ↦ Q u ω) := by
    intro u v huv
    change Q u ω ≤ Q v ω
    rw [hQeq, hQeq]
    apply Nat.cast_le.mpr
    apply hN.monotone ω
    apply WithTop.coe_le_coe.mp
    rw [coe_cappedStoppingValue, coe_cappedStoppingValue]
    exact min_le_min_left _ (WithTop.coe_le_coe.mpr huv)
  have hQb (u : ℝ≥0) (ω : Ω) : ‖Q u ω‖ ≤ (m : ℝ) := by
    rw [hQeq, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact_mod_cast hNm _ ω
  have hH2 := countBefore_twice_add_one_boundedSimplePredictable hN hNm
  have hI2 := hmask.mul_process hH2
  have hAm (ω : Ω) : Measurable (fun u ↦ throughStopMask τ u ω * Λ u ω) :=
    ((hmask.1.mul hΛ.predictable).mono (predictable_le_ambient F)).measurable.comp
      (measurable_id.prodMk measurable_const)
  have hAint (u : ℝ≥0) (ω : Ω) :=
    hmask.isBoundedPredictable.integrableOn_mul_intensity hΛ u ω
  have hDint (u : ℝ≥0) (ω : Ω) :=
    hI2.isBoundedPredictable.integrableOn_mul_intensity hΛ u ω
  have hAdiff (ω : Ω) : A t ω - A s ω =
      ∫ u in Ioc s t, throughStopMask τ u ω * Λ u ω ∂timeMeasure := by
    have hh := setIntegral_Ioc_eq_integratedIntensity_one_sub (Ω := Unit)
      (Λ := fun u _ ↦ throughStopMask τ u ω * Λ u ω) (ω := ()) hst (hAint t ω)
    simpa only [A, integratedIntensity, one_mul] using hh.symm
  have hDdiff (ω : Ω) : D t ω - D s ω =
      ∫ u in Ioc s t,
        (throughStopMask τ u ω * (2 * (countBefore N u ω : ℝ) + 1)) * Λ u ω ∂timeMeasure := by
    have hh := setIntegral_Ioc_eq_integratedIntensity_one_sub (Ω := Unit)
      (Λ := fun u _ ↦ (throughStopMask τ u ω * (2 * (countBefore N u ω : ℝ) + 1)) *
        Λ u ω) (ω := ()) hst (hDint t ω)
    simpa only [D, integratedIntensity, one_mul] using hh.symm
  have hAb (ω : Ω) : A t ω - A s ω ≤ C * ((t : ℝ) - s) := by
    have hh := norm_setIntegral_zero_sub_le (hAm ω) hC
      (throughStopMask_rate_bound_ae hC (fun u ↦ hΛ.nonneg u ω)
        (fun u hu ↦ hcap u ω hu)) hst
    exact (le_abs_self _).trans hh
  apply integral_sq_count_increment_le_of_compensators hQ hQb
    (stoppedCount_compensated_martingale hN hΛ hmask)
    (stoppedCount_square_compensated_martingale hN hΛ hNm hmask) hst
    (mul_nonneg hC (sub_nonneg.mpr (show (s : ℝ) ≤ t from hst))) hAb
  intro ω
  have hsI : Ioc s t ⊆ Ioc (0 : ℝ≥0) t := by
    intro u hu; exact ⟨lt_of_le_of_lt bot_le hu.1, hu.2⟩
  have hiR := (hAint t ω).mono_set hsI
  have hiD := (hDint t ω).mono_set hsI
  have heq : D t ω - D s ω - 2 * Q s ω * (A t ω - A s ω) =
      ∫ u in Ioc s t,
        ((throughStopMask τ u ω * (2 * (countBefore N u ω : ℝ) + 1)) * Λ u ω -
          (2 * Q s ω) * (throughStopMask τ u ω * Λ u ω)) ∂timeMeasure := by
    rw [hDdiff, hAdiff, integral_sub hiD (hiR.const_mul _), integral_const_mul]
  rw [heq]
  calc
    _ ≤ ∫ u in Ioc s t,
        (2 * (Q t ω - Q s ω) + 1) * (throughStopMask τ u ω * Λ u ω) ∂timeMeasure := by
      apply setIntegral_mono_on (hiD.sub (hiR.const_mul _)) (hiR.const_mul _)
        measurableSet_Ioc
      intro u hu
      change (throughStopMask τ u ω * (2 * (countBefore N u ω : ℝ) + 1)) * Λ u ω -
        (2 * Q s ω) * (throughStopMask τ u ω * Λ u ω) ≤
          (2 * (Q t ω - Q s ω) + 1) * (throughStopMask τ u ω * Λ u ω)
      by_cases hstop : (u : WithTop ℝ≥0) ≤ τ ω
      · have huq : u ≤ cappedStoppingValue t τ ω := by
          apply WithTop.coe_le_coe.mp
          rw [coe_cappedStoppingValue]
          exact le_min hstop (WithTop.coe_le_coe.mpr hu.2)
        have hleft : (countBefore N u ω : ℝ) ≤ Q t ω := by
          rw [hQeq]
          exact_mod_cast (hN.countBefore_le_at u ω).trans (hN.monotone ω huq)
        simp only [throughStopMask, ite_eq_left hstop, one_mul]
        nlinarith [hΛ.nonneg u ω]
      · have hz : throughStopMask τ u ω = 0 := ite_eq_right hstop
        rw [hz]
        norm_num
    _ = (2 * (Q t ω - Q s ω) + 1) * (A t ω - A s ω) := by
      rw [integral_const_mul, ← hAdiff]
    _ ≤ (2 * (Q t ω - Q s ω) + 1) * (C * ((t : ℝ) - s)) :=
      mul_le_mul_of_nonneg_left (hAb ω) (by linarith [hQmono ω hst])

theorem integral_factorial_stoppedCount_increment_le
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {N : ℝ≥0 → Ω → ℕ} {Λ : ℝ≥0 → Ω → ℝ}
    (hN : IsSimpleCountingProcess F N) (hΛ : HasPredictableIntensity μ F N Λ)
    {m : ℕ} (hNm : ∀ u ω, N u ω ≤ m)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ)
    (hmask : IsBoundedSimplePredictable F (throughStopMask τ))
    {C : ℝ} (hC : 0 ≤ C) (hcap : ∀ (u : ℝ≥0) (ω : Ω), (u : WithTop ℝ≥0) < τ ω → Λ u ω ≤ C)
    {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ ω, (stoppedProcess (fun u ω ↦ (N u ω : ℝ)) τ t ω -
      stoppedProcess (fun u ω ↦ (N u ω : ℝ)) τ s ω)^2 -
      (stoppedProcess (fun u ω ↦ (N u ω : ℝ)) τ t ω -
        stoppedProcess (fun u ω ↦ (N u ω : ℝ)) τ s ω) ∂μ) ≤
        2 * (C * ((t : ℝ) - s))^2 := by
  let Q := stoppedProcess (fun u ω ↦ (N u ω : ℝ)) τ
  let A := integratedIntensity Λ (throughStopMask τ)
  let D := integratedIntensity Λ (fun u ω ↦
    throughStopMask τ u ω * (2 * (countBefore N u ω : ℝ) + 1))
  have hQ : StronglyAdapted F Q := by
    change StronglyAdapted F (stoppedProcess (fun u ω ↦ (N u ω : ℝ)) τ)
    rw [Limit.stoppedProcess_eq_cappedStoppingValue]
    exact Limit.stronglyAdapted_cappedStoppingValue_of_rightContinuous
      hN.stronglyAdapted hτ hN.rightContinuous
  have hQeq (u : ℝ≥0) (ω : Ω) : Q u ω = (N (cappedStoppingValue u τ ω) ω : ℝ) := by
    change stoppedProcess (fun u ω ↦ (N u ω : ℝ)) τ u ω = _
    rw [Limit.stoppedProcess_eq_cappedStoppingValue]
  have hQmono (ω : Ω) : Monotone (fun u ↦ Q u ω) := by
    intro u v huv
    change Q u ω ≤ Q v ω
    rw [hQeq, hQeq]
    apply Nat.cast_le.mpr
    apply hN.monotone ω
    apply WithTop.coe_le_coe.mp
    rw [coe_cappedStoppingValue, coe_cappedStoppingValue]
    exact min_le_min_left _ (WithTop.coe_le_coe.mpr huv)
  have hQb (u : ℝ≥0) (ω : Ω) : ‖Q u ω‖ ≤ (m : ℝ) := by
    rw [hQeq, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact_mod_cast hNm _ ω
  have hH2 := countBefore_twice_add_one_boundedSimplePredictable hN hNm
  have hI2 := hmask.mul_process hH2
  have hAm (ω : Ω) : Measurable (fun u ↦ throughStopMask τ u ω * Λ u ω) :=
    ((hmask.1.mul hΛ.predictable).mono (predictable_le_ambient F)).measurable.comp
      (measurable_id.prodMk measurable_const)
  have hAint (u : ℝ≥0) (ω : Ω) :=
    hmask.isBoundedPredictable.integrableOn_mul_intensity hΛ u ω
  have hDint (u : ℝ≥0) (ω : Ω) :=
    hI2.isBoundedPredictable.integrableOn_mul_intensity hΛ u ω
  have hAdiff (ω : Ω) : A t ω - A s ω =
      ∫ u in Ioc s t, throughStopMask τ u ω * Λ u ω ∂timeMeasure := by
    have hh := setIntegral_Ioc_eq_integratedIntensity_one_sub (Ω := Unit)
      (Λ := fun u _ ↦ throughStopMask τ u ω * Λ u ω) (ω := ()) hst (hAint t ω)
    simpa only [A, integratedIntensity, one_mul] using hh.symm
  have hDdiff (ω : Ω) : D t ω - D s ω =
      ∫ u in Ioc s t,
        (throughStopMask τ u ω * (2 * (countBefore N u ω : ℝ) + 1)) * Λ u ω ∂timeMeasure := by
    have hh := setIntegral_Ioc_eq_integratedIntensity_one_sub (Ω := Unit)
      (Λ := fun u _ ↦ (throughStopMask τ u ω * (2 * (countBefore N u ω : ℝ) + 1)) *
        Λ u ω) (ω := ()) hst (hDint t ω)
    simpa only [D, integratedIntensity, one_mul] using hh.symm
  have hAb (ω : Ω) : A t ω - A s ω ≤ C * ((t : ℝ) - s) := by
    have hh := norm_setIntegral_zero_sub_le (hAm ω) hC
      (throughStopMask_rate_bound_ae hC (fun u ↦ hΛ.nonneg u ω)
        (fun u hu ↦ hcap u ω hu)) hst
    exact (le_abs_self _).trans hh
  apply integral_factorial_count_increment_le_of_compensators hQ hQb
    (stoppedCount_compensated_martingale hN hΛ hmask)
    (stoppedCount_square_compensated_martingale hN hΛ hNm hmask) hst
    (mul_nonneg hC (sub_nonneg.mpr (show (s : ℝ) ≤ t from hst))) hAb
  intro ω
  have hsI : Ioc s t ⊆ Ioc (0 : ℝ≥0) t := by
    intro u hu; exact ⟨lt_of_le_of_lt bot_le hu.1, hu.2⟩
  have hiR := (hAint t ω).mono_set hsI
  have hiD := (hDint t ω).mono_set hsI
  have heq : D t ω - D s ω - 2 * Q s ω * (A t ω - A s ω) =
      ∫ u in Ioc s t,
        ((throughStopMask τ u ω * (2 * (countBefore N u ω : ℝ) + 1)) * Λ u ω -
          (2 * Q s ω) * (throughStopMask τ u ω * Λ u ω)) ∂timeMeasure := by
    rw [hDdiff, hAdiff, integral_sub hiD (hiR.const_mul _), integral_const_mul]
  rw [heq]
  calc
    _ ≤ ∫ u in Ioc s t,
        (2 * (Q t ω - Q s ω) + 1) * (throughStopMask τ u ω * Λ u ω) ∂timeMeasure := by
      apply setIntegral_mono_on (hiD.sub (hiR.const_mul _)) (hiR.const_mul _)
        measurableSet_Ioc
      intro u hu
      change (throughStopMask τ u ω * (2 * (countBefore N u ω : ℝ) + 1)) * Λ u ω -
        (2 * Q s ω) * (throughStopMask τ u ω * Λ u ω) ≤
          (2 * (Q t ω - Q s ω) + 1) * (throughStopMask τ u ω * Λ u ω)
      by_cases hstop : (u : WithTop ℝ≥0) ≤ τ ω
      · have huq : u ≤ cappedStoppingValue t τ ω := by
          apply WithTop.coe_le_coe.mp
          rw [coe_cappedStoppingValue]
          exact le_min hstop (WithTop.coe_le_coe.mpr hu.2)
        have hleft : (countBefore N u ω : ℝ) ≤ Q t ω := by
          rw [hQeq]
          exact_mod_cast (hN.countBefore_le_at u ω).trans (hN.monotone ω huq)
        simp only [throughStopMask, ite_eq_left hstop, one_mul]
        nlinarith [hΛ.nonneg u ω]
      · have hz : throughStopMask τ u ω = 0 := ite_eq_right hstop
        rw [hz]
        norm_num
    _ = (2 * (Q t ω - Q s ω) + 1) * (A t ω - A s ω) := by
      rw [integral_const_mul, ← hAdiff]
    _ ≤ 2 * (C * ((t : ℝ) - s)) * (Q t ω - Q s ω) + (A t ω - A s ω) := by
      have hh := mul_le_mul_of_nonneg_left (hAb ω)
        (show 0 ≤ 2 * (Q t ω - Q s ω) by linarith [hQmono ω hst])
      nlinarith

end OTSelector.CountingProcess

namespace OTSelector.FiniteSample

open CountingProcess
variable {n : ℕ} {lam : ℝ}

/-- The actual stopped source count has a local second moment uniform in sample size. -/
theorem integral_sq_safeSourceA1Count_increment_le
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    {eta B x0 p0 : ℝ} (hn : 0 < n) (hB : 0 < B) (heta : 0 ≤ eta)
    (hetaSmall : eta * (2 + lam) ≤ lam) (T : ℝ≥0)
    {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ ω : FiniteSample n, (stoppedProcess (fun u ω ↦
      (safeSourceBulkCount hlam0.le (by linarith) B x0 p0 u ω : ℝ))
        (safeFeedbackA1StopTime hlam0.le (by linarith) eta B x0 p0 T) t ω -
      stoppedProcess (fun u ω ↦
      (safeSourceBulkCount hlam0.le (by linarith) B x0 p0 u ω : ℝ))
        (safeFeedbackA1StopTime hlam0.le (by linarith) eta B x0 p0 T) s ω)^2
          ∂(finiteSampleLaw n)) ≤
      3 * ((t : ℝ) - s) + 18 * ((t : ℝ) - s)^2 := by
  have hlamHalf : lam < 1 / 2 := by linarith
  have hmask := safeFeedbackA1ThroughStopMask_boundedSimplePredictable
    (n := n) hlam0.le hlamHalf hB eta x0 p0 T
  have heq : safeFeedbackA1ThroughStopMask (n := n) hlam0.le hlamHalf eta B x0 p0 T =
      throughStopMask (safeFeedbackA1StopTime hlam0.le hlamHalf eta B x0 p0 T) := by
    funext u ω
    exact safeFeedbackA1ThroughStopMask_eq_throughStopMask hlam0.le hlamHalf eta B x0 p0 T u ω
  rw [heq] at hmask
  have h := integral_sq_stoppedCount_increment_le
    (safeSourceBulkCount_isSimpleCountingProcess (n := n) hlam0.le hlamHalf B x0 p0)
    (safeSourceBulkCount_hasPredictableIntensity (x0 := x0) (p0 := p0) hlam0.le hlamHalf hn hB)
    (fun u ω ↦ finiteEventCountTop_le
      (fun i ↦ safeSourceBulkEventTime hlam0.le hlamHalf B x0 p0 i) u ω)
    (safeFeedbackA1StopTime_isStoppingTime hlam0.le hlamHalf hB eta x0 p0 T)
    hmask (by norm_num : (0 : ℝ) ≤ 3)
    (fun u ω hu ↦ (safeFeedbackSpatial_rates_le_of_lt_stop
      hlam0 hlam hB heta hetaSmall T u ω hu).1) hst
  convert h using 1; ring

/-- The actual stopped target count has a local second moment uniform in sample size. -/
theorem integral_sq_safeTargetA1Count_increment_le
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    {eta B x0 p0 : ℝ} (hn : 0 < n) (hB : 0 < B) (heta : 0 ≤ eta)
    (hetaSmall : eta * (2 + lam) ≤ lam) (T : ℝ≥0)
    {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ ω : FiniteSample n, (stoppedProcess (fun u ω ↦
      (safeTargetBulkCount hlam0.le (by linarith) B x0 p0 u ω : ℝ))
        (safeFeedbackA1StopTime hlam0.le (by linarith) eta B x0 p0 T) t ω -
      stoppedProcess (fun u ω ↦
      (safeTargetBulkCount hlam0.le (by linarith) B x0 p0 u ω : ℝ))
        (safeFeedbackA1StopTime hlam0.le (by linarith) eta B x0 p0 T) s ω)^2
          ∂(finiteSampleLaw n)) ≤
      3 * ((t : ℝ) - s) + 18 * ((t : ℝ) - s)^2 := by
  have hlamHalf : lam < 1 / 2 := by linarith
  have hmask := safeFeedbackA1ThroughStopMask_boundedSimplePredictable
    (n := n) hlam0.le hlamHalf hB eta x0 p0 T
  have heq : safeFeedbackA1ThroughStopMask (n := n) hlam0.le hlamHalf eta B x0 p0 T =
      throughStopMask (safeFeedbackA1StopTime hlam0.le hlamHalf eta B x0 p0 T) := by
    funext u ω
    exact safeFeedbackA1ThroughStopMask_eq_throughStopMask hlam0.le hlamHalf eta B x0 p0 T u ω
  rw [heq] at hmask
  have h := integral_sq_stoppedCount_increment_le
    (safeTargetBulkCount_isSimpleCountingProcess (n := n) hlam0.le hlamHalf B x0 p0)
    (safeTargetBulkCount_hasPredictableIntensity (x0 := x0) (p0 := p0) hlam0.le hlamHalf hn hB)
    (fun u ω ↦ finiteEventCountTop_le
      (fun i ↦ safeTargetBulkEventTime hlam0.le hlamHalf B x0 p0 i) u ω)
    (safeFeedbackA1StopTime_isStoppingTime hlam0.le hlamHalf hB eta x0 p0 T)
    hmask (by norm_num : (0 : ℝ) ≤ 3)
    (fun u ω hu ↦ (safeFeedbackSpatial_rates_le_of_lt_stop
      hlam0 hlam hB heta hetaSmall T u ω hu).2) hst
  convert h using 1; ring


/-- The genuine stopped count has a quadratic factorial-window bound. -/
theorem integral_factorial_safeSourceA1Count_increment_le
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    {eta B x0 p0 : ℝ} (hn : 0 < n) (hB : 0 < B) (heta : 0 ≤ eta)
    (hetaSmall : eta * (2 + lam) ≤ lam) (T : ℝ≥0)
    {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ ω : FiniteSample n, (stoppedProcess (fun u ω ↦
      (safeSourceBulkCount hlam0.le (by linarith) B x0 p0 u ω : ℝ))
        (safeFeedbackA1StopTime hlam0.le (by linarith) eta B x0 p0 T) t ω -
      stoppedProcess (fun u ω ↦
      (safeSourceBulkCount hlam0.le (by linarith) B x0 p0 u ω : ℝ))
        (safeFeedbackA1StopTime hlam0.le (by linarith) eta B x0 p0 T) s ω)^2
      - (stoppedProcess (fun u ω ↦
      (safeSourceBulkCount hlam0.le (by linarith) B x0 p0 u ω : ℝ))
        (safeFeedbackA1StopTime hlam0.le (by linarith) eta B x0 p0 T) t ω -
      stoppedProcess (fun u ω ↦
      (safeSourceBulkCount hlam0.le (by linarith) B x0 p0 u ω : ℝ))
        (safeFeedbackA1StopTime hlam0.le (by linarith) eta B x0 p0 T) s ω)
          ∂(finiteSampleLaw n)) ≤ 18 * ((t : ℝ) - s)^2 := by
  have hlamHalf : lam < 1 / 2 := by linarith
  have hmask := safeFeedbackA1ThroughStopMask_boundedSimplePredictable
    (n := n) hlam0.le hlamHalf hB eta x0 p0 T
  have heq : safeFeedbackA1ThroughStopMask (n := n) hlam0.le hlamHalf eta B x0 p0 T =
      throughStopMask (safeFeedbackA1StopTime hlam0.le hlamHalf eta B x0 p0 T) := by
    funext u ω
    exact safeFeedbackA1ThroughStopMask_eq_throughStopMask hlam0.le hlamHalf eta B x0 p0 T u ω
  rw [heq] at hmask
  have h := integral_factorial_stoppedCount_increment_le
    (safeSourceBulkCount_isSimpleCountingProcess (n := n) hlam0.le hlamHalf B x0 p0)
    (safeSourceBulkCount_hasPredictableIntensity (x0 := x0) (p0 := p0) hlam0.le hlamHalf hn hB)
    (fun u ω ↦ finiteEventCountTop_le
      (fun i ↦ safeSourceBulkEventTime hlam0.le hlamHalf B x0 p0 i) u ω)
    (safeFeedbackA1StopTime_isStoppingTime hlam0.le hlamHalf hB eta x0 p0 T)
    hmask (by norm_num : (0 : ℝ) ≤ 3)
    (fun u ω hu ↦ (safeFeedbackSpatial_rates_le_of_lt_stop
      hlam0 hlam hB heta hetaSmall T u ω hu).1) hst
  convert h using 1; ring

/-- The genuine stopped count has a quadratic factorial-window bound. -/
theorem integral_factorial_safeTargetA1Count_increment_le
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    {eta B x0 p0 : ℝ} (hn : 0 < n) (hB : 0 < B) (heta : 0 ≤ eta)
    (hetaSmall : eta * (2 + lam) ≤ lam) (T : ℝ≥0)
    {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ ω : FiniteSample n, (stoppedProcess (fun u ω ↦
      (safeTargetBulkCount hlam0.le (by linarith) B x0 p0 u ω : ℝ))
        (safeFeedbackA1StopTime hlam0.le (by linarith) eta B x0 p0 T) t ω -
      stoppedProcess (fun u ω ↦
      (safeTargetBulkCount hlam0.le (by linarith) B x0 p0 u ω : ℝ))
        (safeFeedbackA1StopTime hlam0.le (by linarith) eta B x0 p0 T) s ω)^2
      - (stoppedProcess (fun u ω ↦
      (safeTargetBulkCount hlam0.le (by linarith) B x0 p0 u ω : ℝ))
        (safeFeedbackA1StopTime hlam0.le (by linarith) eta B x0 p0 T) t ω -
      stoppedProcess (fun u ω ↦
      (safeTargetBulkCount hlam0.le (by linarith) B x0 p0 u ω : ℝ))
        (safeFeedbackA1StopTime hlam0.le (by linarith) eta B x0 p0 T) s ω)
          ∂(finiteSampleLaw n)) ≤ 18 * ((t : ℝ) - s)^2 := by
  have hlamHalf : lam < 1 / 2 := by linarith
  have hmask := safeFeedbackA1ThroughStopMask_boundedSimplePredictable
    (n := n) hlam0.le hlamHalf hB eta x0 p0 T
  have heq : safeFeedbackA1ThroughStopMask (n := n) hlam0.le hlamHalf eta B x0 p0 T =
      throughStopMask (safeFeedbackA1StopTime hlam0.le hlamHalf eta B x0 p0 T) := by
    funext u ω
    exact safeFeedbackA1ThroughStopMask_eq_throughStopMask hlam0.le hlamHalf eta B x0 p0 T u ω
  rw [heq] at hmask
  have h := integral_factorial_stoppedCount_increment_le
    (safeTargetBulkCount_isSimpleCountingProcess (n := n) hlam0.le hlamHalf B x0 p0)
    (safeTargetBulkCount_hasPredictableIntensity (x0 := x0) (p0 := p0) hlam0.le hlamHalf hn hB)
    (fun u ω ↦ finiteEventCountTop_le
      (fun i ↦ safeTargetBulkEventTime hlam0.le hlamHalf B x0 p0 i) u ω)
    (safeFeedbackA1StopTime_isStoppingTime hlam0.le hlamHalf hB eta x0 p0 T)
    hmask (by norm_num : (0 : ℝ) ≤ 3)
    (fun u ω hu ↦ (safeFeedbackSpatial_rates_le_of_lt_stop
      hlam0 hlam hB heta hetaSmall T u ω hu).2) hst
  convert h using 1; ring

end OTSelector.FiniteSample
