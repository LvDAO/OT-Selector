import OTSelector.Feedback.BoundaryEnergy
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

namespace OTSelector.Probability

variable {ι E : Type*} [Fintype ι] [MeasurableSpace E]

noncomputable def finiteProductIndicator
    (A : ι → Set E) (i : ι) (ω : ι → E) : ℝ :=
  (A i).indicator (fun _ : E ↦ (1 : ℝ)) (ω i)

omit [Fintype ι] in
theorem measurable_finiteProductIndicator
    (A : ι → Set E) (hA : ∀ i, MeasurableSet (A i)) (i : ι) :
    Measurable (finiteProductIndicator A i) := by
  exact (measurable_const.indicator (hA i)).comp (measurable_pi_apply i)

theorem integrable_finiteProductIndicator
    (P : ι → Measure E) [∀ i, IsProbabilityMeasure (P i)]
    (A : ι → Set E) (hA : ∀ i, MeasurableSet (A i)) (i : ι) :
    Integrable (finiteProductIndicator A i) (Measure.pi P) := by
  change Integrable (fun ω : ι → E ↦
    (A i).indicator (fun _ : E ↦ (1 : ℝ)) (ω i)) (Measure.pi P)
  simpa [Function.comp_def] using
    (measurePreserving_eval P i).integrable_comp_of_integrable
      ((integrable_const (1 : ℝ)).indicator (hA i))

theorem integral_finiteProductIndicator
    (P : ι → Measure E) [∀ i, IsProbabilityMeasure (P i)]
    (A : ι → Set E) (hA : ∀ i, MeasurableSet (A i)) (i : ι) :
    ∫ ω, finiteProductIndicator A i ω ∂Measure.pi P = (P i).real (A i) := by
  change ∫ ω : ι → E, (A i).indicator (fun _ : E ↦ (1 : ℝ)) (ω i) ∂Measure.pi P = _
  rw [MeasureTheory.integral_comp_eval
    ((measurable_const.indicator (hA i)).aestronglyMeasurable)]
  exact integral_indicator_one (hA i)

omit [Fintype ι] [MeasurableSpace E] in
theorem finiteProductIndicator_sq
    (A : ι → Set E) (i : ι) :
    (fun ω : ι → E ↦ finiteProductIndicator A i ω ^ 2) = finiteProductIndicator A i := by
  funext ω
  by_cases hω : ω i ∈ A i <;> simp [finiteProductIndicator, hω]

theorem integral_sq_const_add_signedIndicatorSum_le
    {ι E : Type*} [Fintype ι] [MeasurableSpace E]
    (P : ι → Measure E) [∀ i, IsProbabilityMeasure (P i)]
    (A : ι → Set E) (hA : ∀ i, MeasurableSet (A i))
    (sign : ι → ℝ) (hsign : ∀ i, sign i = 1 ∨ sign i = -1)
    (K0 : ℝ) :
  ∫ ω : ι → E,
      (K0 + ∑ i, sign i * if ω i ∈ A i then (1 : ℝ) else 0)^2
      ∂Measure.pi P
    ≤ (∑ i, (P i).real (A i)) +
      (K0 + ∑ i, sign i * (P i).real (A i))^2 := by
  classical
  let μ : Measure (ι → E) := Measure.pi P
  let X : ι → (ι → E) → ℝ := finiteProductIndicator A
  let p : ι → ℝ := fun i ↦ (P i).real (A i)
  let Z : ι → (ι → E) → ℝ := fun i ω ↦ sign i * (X i ω - p i)
  let C : ℝ := K0 + ∑ i, sign i * p i
  have hX_meas : ∀ i, Measurable (X i) := by
    intro i
    exact measurable_finiteProductIndicator A hA i
  have hX_int : ∀ i, Integrable (X i) μ := by
    intro i
    simpa [X, μ] using integrable_finiteProductIndicator P A hA i
  have hX_integral : ∀ i, ∫ ω, X i ω ∂μ = p i := by
    intro i
    simpa [X, p, μ] using integral_finiteProductIndicator P A hA i
  have hX_sq : ∀ i, (fun ω ↦ X i ω ^ 2) = X i := by
    intro i
    simpa [X] using finiteProductIndicator_sq A i
  have hEval_indep : iIndepFun (fun i (ω : ι → E) ↦ ω i) μ := by
    dsimp [μ]
    exact iIndepFun_pi fun _ ↦ measurable_id.aemeasurable
  have hX_indep : iIndepFun X μ := by
    have h := hEval_indep.comp
      (fun i ↦ (A i).indicator (fun _ : E ↦ (1 : ℝ)))
      (fun i ↦ measurable_const.indicator (hA i))
    change iIndepFun (fun i (ω : ι → E) ↦
      (A i).indicator (fun _ : E ↦ (1 : ℝ)) (ω i)) μ
    exact h
  have hZ_meas : ∀ i, Measurable (Z i) := by
    intro i
    exact (hX_meas i).sub measurable_const |>.const_mul (sign i)
  have hp_nonneg : ∀ i, 0 ≤ p i := by
    intro i
    exact measureReal_nonneg
  have hp_le_one : ∀ i, p i ≤ 1 := by
    intro i
    exact measureReal_le_one
  have hZ_bound : ∀ i ω, ‖Z i ω‖ ≤ (1 : ℝ) := by
    intro i ω
    change ‖sign i * (X i ω - p i)‖ ≤ (1 : ℝ)
    rcases hsign i with hi | hi
    · rw [hi, one_mul, Real.norm_eq_abs]
      by_cases hω : ω i ∈ A i
      · simp [X, finiteProductIndicator, hω, abs_le]
        constructor <;> linarith [hp_nonneg i, hp_le_one i]
      · simp [X, finiteProductIndicator, hω, abs_le]
        constructor <;> linarith [hp_nonneg i, hp_le_one i]
    · rw [hi, neg_one_mul, Real.norm_eq_abs, abs_neg]
      by_cases hω : ω i ∈ A i
      · simp [X, finiteProductIndicator, hω, abs_le]
        constructor <;> linarith [hp_nonneg i, hp_le_one i]
      · simp [X, finiteProductIndicator, hω, abs_le]
        constructor <;> linarith [hp_nonneg i, hp_le_one i]
  have hZ_int : ∀ i, Integrable (Z i) μ := by
    intro i
    exact (hX_int i).sub (integrable_const _ ) |>.const_mul (sign i)
  have hZ_sq_int : ∀ i, Integrable (fun ω ↦ Z i ω ^ 2) μ := by
    intro i
    simpa only [pow_two] using
      (hZ_int i).mul_bdd (hZ_meas i).aestronglyMeasurable
        (Filter.Eventually.of_forall (hZ_bound i))
  have hZ_centered : ∀ i, ∫ ω, Z i ω ∂μ = 0 := by
    intro i
    calc
      ∫ ω, Z i ω ∂μ = sign i * (∫ ω, X i ω ∂μ - ∫ _ : ι → E, p i ∂μ) := by
        rw [show (fun ω ↦ Z i ω) =
          (fun ω ↦ sign i * (X i ω - p i)) from rfl]
        rw [integral_const_mul, integral_sub (hX_int i) (integrable_const _)]
      _ = 0 := by simp [hX_integral i, μ, p]
  have hZ_indep : iIndepFun Z μ := by
    have h := hX_indep.comp
      (fun i x ↦ sign i * (x - p i))
      (fun i ↦ measurable_const.mul (measurable_id.sub measurable_const))
    simpa [Z, Function.comp_def] using h
  have hsum_sq :
      ∫ ω, (∑ i, Z i ω) ^ 2 ∂μ = ∑ i, ∫ ω, (Z i ω) ^ 2 ∂μ := by
    simpa using
      OTSelector.integral_sq_finset_sum_eq_sum_integral_sq_of_iIndepFun μ Finset.univ Z
        (fun i _ ↦ hZ_meas i) (fun i _ ↦ hZ_int i) (fun i _ ↦ hZ_sq_int i)
        (fun i _ ↦ hZ_centered i) hZ_indep
  have hsum_centered : ∫ ω, (∑ i, Z i ω) ∂μ = 0 := by
    rw [integral_finsetSum]
    · simp [hZ_centered]
    · intro i hi
      exact hZ_int i
  have hsum_meas : Measurable (fun ω ↦ ∑ i, Z i ω) := by
    fun_prop
  have hsum_bound : ∀ ω, ‖∑ i, Z i ω‖ ≤ (Fintype.card ι : ℝ) := by
    intro ω
    calc
      ‖∑ i, Z i ω‖ ≤ ∑ i, ‖Z i ω‖ := norm_sum_le _ _
      _ ≤ ∑ _i : ι, (1 : ℝ) := Finset.sum_le_sum fun i _ ↦ hZ_bound i ω
      _ = (Fintype.card ι : ℝ) := by simp
  have hsum_int : Integrable (fun ω ↦ ∑ i, Z i ω) μ := by
    exact integrable_finsetSum (Finset.univ : Finset ι) (fun i _ ↦ hZ_int i)
  have hsum_sq_int : Integrable (fun ω ↦ (∑ i, Z i ω) ^ 2) μ := by
    simpa only [pow_two] using
      hsum_int.mul_bdd hsum_meas.aestronglyMeasurable
        (Filter.Eventually.of_forall hsum_bound)
  have hvar_eq : ∀ i, ∫ ω, (Z i ω) ^ 2 ∂μ = p i - p i ^ 2 := by
    intro i
    have hpoint : (fun ω ↦ (Z i ω) ^ 2) =
        (fun ω ↦ X i ω - (2 * p i) * X i ω + p i ^ 2) := by
      funext ω
      by_cases hω : ω i ∈ A i
      · rcases hsign i with hi | hi <;>
          simp [Z, X, finiteProductIndicator, hω, hi] <;> ring
      · rcases hsign i with hi | hi <;>
          simp [Z, X, finiteProductIndicator, hω, hi]
    rw [hpoint]
    calc
      ∫ ω, (X i ω - (2 * p i) * X i ω) + p i ^ 2 ∂μ =
          (∫ ω, X i ω - (2 * p i) * X i ω ∂μ) + ∫ _ : ι → E, p i ^ 2 ∂μ := by
            apply integral_add
            · exact (hX_int i).sub ((hX_int i).const_mul (2 * p i))
            · exact integrable_const _
      _ = p i - p i ^ 2 := by
        have hXi : ∫ ω, X i ω ∂Measure.pi P = p i := by
          simpa [μ] using hX_integral i
        rw [integral_sub (hX_int i) ((hX_int i).const_mul (2 * p i)), hXi,
          integral_const_mul, hXi, integral_const]
        simp [μ]
        ring
  have hvar_le : ∀ i, (∫ ω, (Z i ω) ^ 2 ∂μ) ≤ p i := by
    intro i
    rw [hvar_eq i]
    nlinarith [sq_nonneg (p i)]
  have hvar_sum : (∑ i, ∫ ω, (Z i ω) ^ 2 ∂μ) ≤ ∑ i, p i := by
    exact Finset.sum_le_sum fun i _ ↦ hvar_le i
  have hdecomp : ∀ ω, K0 + ∑ i, sign i * X i ω = C + ∑ i, Z i ω := by
    intro ω
    simp only [C, Z]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    ring
  have hsq_add : ∫ ω, (C + ∑ i, Z i ω) ^ 2 ∂μ = C ^ 2 +
      ∫ ω, (∑ i, Z i ω) ^ 2 ∂μ := by
    have hcross_int : Integrable (fun ω ↦ (2 * C) * ∑ i, Z i ω) μ :=
      hsum_int.const_mul (2 * C)
    have hpoly : (fun ω ↦ (C + ∑ i, Z i ω) ^ 2) =
        (fun ω ↦ C ^ 2 + (2 * C) * ∑ i, Z i ω + (∑ i, Z i ω) ^ 2) := by
      funext ω
      ring
    rw [hpoly]
    calc
      ∫ ω, (C ^ 2 + (2 * C) * ∑ i, Z i ω) + (∑ i, Z i ω) ^ 2 ∂μ =
          (∫ ω, C ^ 2 + (2 * C) * ∑ i, Z i ω ∂μ) +
            ∫ ω, (∑ i, Z i ω) ^ 2 ∂μ := by
              apply integral_add
              · exact (integrable_const _).add hcross_int
              · exact hsum_sq_int
      _ = C ^ 2 + ∫ ω, (∑ i, Z i ω) ^ 2 ∂μ := by
        rw [integral_add (integrable_const _) hcross_int, integral_const,
          integral_const_mul, hsum_centered]
        simp [μ]
  calc
    ∫ ω : ι → E,
        (K0 + ∑ i, sign i * if ω i ∈ A i then (1 : ℝ) else 0)^2 ∂Measure.pi P =
        ∫ ω, (C + ∑ i, Z i ω) ^ 2 ∂μ := by
          classical
          apply integral_congr_ae
          filter_upwards [] with ω
          change (K0 + ∑ i, sign i * X i ω) ^ 2 = (C + ∑ i, Z i ω) ^ 2
          rw [hdecomp ω]
    _ = C ^ 2 + ∫ ω, (∑ i, Z i ω) ^ 2 ∂μ := hsq_add
    _ = C ^ 2 + ∑ i, ∫ ω, (Z i ω) ^ 2 ∂μ := by rw [hsum_sq]
    _ ≤ C ^ 2 + ∑ i, p i := by
      simpa [add_comm] using add_le_add_left hvar_sum (C ^ 2)
    _ = (∑ i, (P i).real (A i)) +
        (K0 + ∑ i, sign i * (P i).real (A i)) ^ 2 := by
      simp [C, p]
      ring

end OTSelector.Probability
