import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Probability.Independence.Integration

/-!
# Boundary energy bookkeeping

This module contains the low-coupling probability and integration layer for boundary estimates.
It expands finite centered sums, proves the Tonelli/Fubini area bound from pointwise second
moments, and combines explicit mean/variance bounds with separate area estimates.  The file does
not construct a boundary count, occupation process, stopping rule, or matching theorem.
-/

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace OTSelector

/-! ### Centered finite sums -/

/--
For centered variables whose off-diagonal products factor through their means, the second moment
of a finite sum is the sum of the individual second moments.  The diagonal and off-diagonal
integrability hypotheses are separate so that callers can expose exactly the estimates they have.
-/
theorem integral_sq_finset_sum_eq_sum_integral_sq_of_uncorrelated
    {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (s : Finset ι) (Z : ι → Ω → ℝ)
    (hZ_sq_int : ∀ i ∈ s, Integrable (fun ω => (Z i ω) ^ 2) P)
    (hZ_prod_int : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Integrable (fun ω => Z i ω * Z j ω) P)
    (hZ_centered : ∀ i ∈ s, ∫ ω, Z i ω ∂P = 0)
    (hZ_uncorr : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ∫ ω, Z i ω * Z j ω ∂P =
        (∫ ω, Z i ω ∂P) * ∫ ω, Z j ω ∂P) :
    ∫ ω, (∑ i ∈ s, Z i ω) ^ 2 ∂P =
      ∑ i ∈ s, ∫ ω, (Z i ω) ^ 2 ∂P := by
  classical
  have hpoint : (fun ω => (∑ i ∈ s, Z i ω) ^ 2) =
      (fun ω => ∑ i ∈ s, ∑ j ∈ s, Z i ω * Z j ω) := by
    funext ω
    rw [pow_two, Finset.sum_mul_sum]
  rw [hpoint]
  rw [integral_finsetSum s]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum s]
    · have hinner : ∑ j ∈ s, ∫ ω, Z i ω * Z j ω ∂P =
          ∫ ω, Z i ω ^ 2 ∂P := by
        rw [← Finset.sum_erase_add s _ hi]
        rw [Finset.sum_eq_zero]
        · simp [pow_two]
        · intro j hj
          have hcross := hZ_uncorr i hi j (Finset.mem_of_mem_erase hj)
            (Finset.ne_of_mem_erase hj).symm
          rw [hZ_centered i hi, hZ_centered j (Finset.mem_of_mem_erase hj), mul_zero] at hcross
          exact hcross
      exact hinner
    · intro j hj
      by_cases hij : i = j
      · subst j
        simpa [pow_two] using hZ_sq_int i hi
      · exact hZ_prod_int i hi j hj hij
  · intro i hi
    apply integrable_finsetSum
    intro j hj
    by_cases hij : i = j
    · subst j
      simpa [pow_two] using hZ_sq_int i hi
    · exact hZ_prod_int i hi j hj hij

/--
Independent centered variables satisfy the preceding factorization by the product-integral
identity.  This is the count-family entry point; `Z` may be a count after subtracting its mean.
-/
theorem integral_sq_finset_sum_eq_sum_integral_sq_of_iIndepFun
    {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (s : Finset ι) (Z : ι → Ω → ℝ)
    (hZ_meas : ∀ i ∈ s, Measurable (Z i))
    (hZ_int : ∀ i ∈ s, Integrable (Z i) P)
    (hZ_sq_int : ∀ i ∈ s, Integrable (fun ω => Z i ω ^ 2) P)
    (hZ_centered : ∀ i ∈ s, ∫ ω, Z i ω ∂P = 0)
    (hZ_indep : iIndepFun Z P) :
    ∫ ω, (∑ i ∈ s, Z i ω) ^ 2 ∂P =
      ∑ i ∈ s, ∫ ω, (Z i ω) ^ 2 ∂P := by
  classical
  apply integral_sq_finset_sum_eq_sum_integral_sq_of_uncorrelated P s Z hZ_sq_int
  · intro i hi j hj hij
    exact (hZ_indep.indepFun hij).integrable_mul (hZ_int i hi) (hZ_int j hj)
  · exact hZ_centered
  · intro i hi j hj hij
    exact (hZ_indep.indepFun hij).integral_fun_mul_eq_mul_integral
      (hZ_meas i hi).aestronglyMeasurable (hZ_meas j hj).aestronglyMeasurable

private theorem integral_id_Ioc_nonneg {B : ℝ} (hB : 0 ≤ B) :
    ∫ x : ℝ in Ioc 0 B, x = B ^ 2 / 2 := by
  rw [← intervalIntegral.integral_of_le hB, integral_id]
  ring

/-! ### Tonelli/Fubini area bounds -/

/--
General area form.  A pointwise bound on the expected square by a nonnegative measurable profile
`q` and an explicit area bound for `q` imply the corresponding expected area bound.  The
pointwise square integrability is retained explicitly; the product integrability needed by
Fubini is derived from the finite Tonelli bound.
-/
theorem expected_area_le_of_pointwise_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {B : ℝ} (K : ℝ → Ω → ℝ) (q : ℝ → ℝ) (Q : ℝ)
    (hK_meas : Measurable (fun p : ℝ × Ω => K p.1 p.2))
    (hK_sq_int : ∀ x ∈ Ioc (0 : ℝ) B,
      Integrable (fun ω => K x ω ^ 2) P)
    (hq_meas : Measurable q)
    (hq_nonneg : ∀ x ∈ Ioc (0 : ℝ) B, 0 ≤ q x)
    (hpoint : ∀ x ∈ Ioc (0 : ℝ) B,
      ∫ ω, K x ω ^ 2 ∂P ≤ q x)
    (hq_int : IntegrableOn q (Ioc (0 : ℝ) B))
    (hq_area : ∫ x : ℝ in Ioc 0 B, q x ≤ Q) :
    ∫ ω, ∫ x : ℝ in Ioc 0 B, K x ω ^ 2 ∂volume ∂P ≤ Q := by
  let μB : Measure ℝ := volume.restrict (Ioc (0 : ℝ) B)
  let F : ℝ × Ω → ℝ := fun p => K p.1 p.2 ^ 2
  have hF_meas : Measurable F := by
    dsimp [F]
    exact hK_meas.pow measurable_const
  have hF_nonneg : ∀ p, 0 ≤ F p := by
    intro p
    dsimp [F]
    exact sq_nonneg _
  have hinner : ∀ x ∈ Ioc (0 : ℝ) B,
      (∫⁻ ω, ENNReal.ofReal (F (x, ω)) ∂P) =
        ENNReal.ofReal (∫ ω, F (x, ω) ∂P) := by
    intro x hx
    have h := ofReal_integral_eq_lintegral_ofReal (hK_sq_int x hx)
      (Filter.Eventually.of_forall (fun ω => sq_nonneg (K x ω)))
    exact h.symm
  have hinner_ae :
      (fun x => ∫⁻ ω, ENNReal.ofReal (F (x, ω)) ∂P) =ᵐ[μB]
        (fun x => ENNReal.ofReal (∫ ω, F (x, ω) ∂P)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with x hx
    exact hinner x hx
  have houter :
      ∫⁻ x : ℝ in Ioc 0 B, ENNReal.ofReal (∫ ω, F (x, ω) ∂P) ≤
        ∫⁻ x : ℝ in Ioc 0 B, ENNReal.ofReal (q x) := by
    apply setLIntegral_mono_ae
    · exact hq_meas.ennreal_ofReal.aemeasurable
    · exact Filter.Eventually.of_forall (fun x hx =>
        ENNReal.ofReal_le_ofReal (by simpa [F] using hpoint x hx))
  have hq_nonneg_ae : 0 ≤ᵐ[μB] q := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with x hx
    exact hq_nonneg x hx
  have hQ_nonneg : 0 ≤ Q := by
    exact (integral_nonneg_of_ae hq_nonneg_ae).trans hq_area
  have hq_l :
      ∫⁻ x : ℝ in Ioc 0 B, ENNReal.ofReal (q x) =
        ENNReal.ofReal (∫ x : ℝ in Ioc 0 B, q x) := by
    exact (ofReal_integral_eq_lintegral_ofReal hq_int.integrable hq_nonneg_ae).symm
  have hprod_le :
      ∫⁻ z, ENNReal.ofReal (F z) ∂(μB.prod P) ≤ ENNReal.ofReal Q := by
    rw [lintegral_prod (fun z => ENNReal.ofReal (F z)) hF_meas.ennreal_ofReal.aemeasurable,
      lintegral_congr_ae hinner_ae]
    calc
      _ ≤ ∫⁻ x : ℝ in Ioc 0 B, ENNReal.ofReal (q x) := houter
      _ = ENNReal.ofReal (∫ x : ℝ in Ioc 0 B, q x) := hq_l
      _ ≤ ENNReal.ofReal Q := ENNReal.ofReal_le_ofReal hq_area
  have hprod_lt :
      ∫⁻ z, ENNReal.ofReal (F z) ∂(μB.prod P) < ⊤ :=
    hprod_le.trans_lt ENNReal.ofReal_lt_top
  have hF_int : Integrable F (μB.prod P) := by
    exact (lintegral_ofReal_ne_top_iff_integrable hF_meas.aestronglyMeasurable
      (Filter.Eventually.of_forall hF_nonneg)).1 (ne_of_lt hprod_lt)
  have hreal_prod : ∫ z, F z ∂(μB.prod P) ≤ Q := by
    have hreal_enn : ENNReal.ofReal (∫ z, F z ∂(μB.prod P)) ≤ ENNReal.ofReal Q := by
      rw [ofReal_integral_eq_lintegral_ofReal hF_int
        (Filter.Eventually.of_forall hF_nonneg)]
      exact hprod_le
    exact (ENNReal.ofReal_le_ofReal_iff hQ_nonneg).mp hreal_enn
  rw [integral_prod_symm F hF_int] at hreal_prod
  exact hreal_prod

/--
The linear profile used for left-boundary counts: `E[K(x)^2] ≤ C*x` integrates to `C B²/2`.
-/
theorem expected_area_le_of_linear_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (K : ℝ → Ω → ℝ)
    (hK_meas : Measurable (fun p : ℝ × Ω => K p.1 p.2))
    (hK_sq_int : ∀ x ∈ Ioc (0 : ℝ) B,
      Integrable (fun ω => K x ω ^ 2) P)
    (hpoint : ∀ x ∈ Ioc (0 : ℝ) B,
      ∫ ω, K x ω ^ 2 ∂P ≤ C * x) :
    ∫ ω, ∫ x : ℝ in Ioc 0 B, K x ω ^ 2 ∂volume ∂P ≤ C * B ^ 2 / 2 := by
  have hq_meas : Measurable (fun x : ℝ => C * x) :=
    measurable_const.mul measurable_id
  have hq_nonneg : ∀ x ∈ Ioc (0 : ℝ) B, 0 ≤ C * x := by
    intro x hx
    exact mul_nonneg hC (mem_Ioc.mp hx).1.le
  have hq_int : IntegrableOn (fun x : ℝ => C * x) (Ioc (0 : ℝ) B) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hB]
    exact (continuousOn_const.mul continuousOn_id).intervalIntegrable
  have hid : ∫ x : ℝ in Ioc 0 B, x = B ^ 2 / 2 :=
    integral_id_Ioc_nonneg hB
  have hq_area : ∫ x : ℝ in Ioc 0 B, C * x = C * B ^ 2 / 2 := by
    rw [integral_const_mul, hid]
    ring
  exact expected_area_le_of_pointwise_bound P K (fun x : ℝ => C * x)
    (C * B ^ 2 / 2) hK_meas hK_sq_int hq_meas hq_nonneg hpoint hq_int hq_area.le

/-! ### Right-tail mean and variance bounds -/

/--
An explicit mean/variance profile yields an integrated second-moment bound.  The area estimate is
provided for `v + m²`; the separate-area corollary below exposes the common `v` and `m²` inputs.
-/
theorem expected_area_sq_le_of_mean_variance
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {B Q : ℝ} (R : ℝ → Ω → ℝ) (m v : ℝ → ℝ)
    (hR_meas : Measurable (fun p : ℝ × Ω => R p.1 p.2))
    (hR_int : ∀ x ∈ Ioc (0 : ℝ) B, Integrable (R x) P)
    (hR_sq_int : ∀ x ∈ Ioc (0 : ℝ) B,
      Integrable (fun ω => R x ω ^ 2) P)
    (hD_sq_int : ∀ x ∈ Ioc (0 : ℝ) B,
      Integrable (fun ω => (R x ω - m x) ^ 2) P)
    (hmean : ∀ x ∈ Ioc (0 : ℝ) B, ∫ ω, R x ω ∂P = m x)
    (hvar : ∀ x ∈ Ioc (0 : ℝ) B,
      ∫ ω, (R x ω - m x) ^ 2 ∂P ≤ v x)
    (hv_nonneg : ∀ x ∈ Ioc (0 : ℝ) B, 0 ≤ v x)
    (hm_meas : Measurable m) (hv_meas : Measurable v)
    (hq_int : IntegrableOn (fun x => v x + (m x) ^ 2) (Ioc (0 : ℝ) B))
    (hq_area : ∫ x : ℝ in Ioc 0 B, v x + (m x) ^ 2 ≤ Q) :
    ∫ ω, ∫ x : ℝ in Ioc 0 B, R x ω ^ 2 ∂volume ∂P ≤ Q := by
  have hq_meas : Measurable (fun x : ℝ => v x + (m x) ^ 2) :=
    hv_meas.add (hm_meas.pow measurable_const)
  have hq_nonneg : ∀ x ∈ Ioc (0 : ℝ) B, 0 ≤ v x + (m x) ^ 2 := by
    intro x hx
    exact add_nonneg (hv_nonneg x hx) (sq_nonneg _)
  apply expected_area_le_of_pointwise_bound P R
    (fun x : ℝ => v x + (m x) ^ 2) Q
    hR_meas hR_sq_int hq_meas hq_nonneg
  · intro x hx
    have hD_int : Integrable (fun ω => R x ω - m x) P :=
      (hR_int x hx).sub (integrable_const (m x))
    have hD_mean : ∫ ω, R x ω - m x ∂P = 0 := by
      rw [integral_sub (hR_int x hx) (integrable_const (m x)), hmean x hx,
        integral_const, probReal_univ, one_smul]
      ring
    have h2D_int : Integrable (fun ω => 2 * (m x) * (R x ω - m x)) P := by
      exact hD_int.const_mul (2 * m x)
    have hconst_int : Integrable (fun _ : Ω => (m x) ^ 2) P :=
      integrable_const _
    have hsecond_eq :
        ∫ ω, R x ω ^ 2 ∂P =
          (∫ ω, (R x ω - m x) ^ 2 ∂P) + (m x) ^ 2 := by
      calc
        ∫ ω, R x ω ^ 2 ∂P =
            ∫ ω, ((R x ω - m x) ^ 2 +
              2 * (m x) * (R x ω - m x) + (m x) ^ 2) ∂P := by
                apply integral_congr_ae
                filter_upwards [] with ω
                ring
        _ = (∫ ω, (R x ω - m x) ^ 2 ∂P) +
              (∫ ω, 2 * (m x) * (R x ω - m x) ∂P) +
              ∫ _ : Ω, (m x) ^ 2 ∂P := by
                have hs₁ := integral_add (μ := P)
                  (f := fun ω => (R x ω - m x) ^ 2 +
                    2 * (m x) * (R x ω - m x))
                  (g := fun _ : Ω => (m x) ^ 2)
                  (hD_sq_int x hx |>.add h2D_int) hconst_int
                have hs₂ := integral_add (μ := P)
                  (f := fun ω => (R x ω - m x) ^ 2)
                  (g := fun ω => 2 * (m x) * (R x ω - m x))
                  (hD_sq_int x hx) h2D_int
                simpa only [Pi.add_apply] using hs₁.trans (congrArg (fun z => z +
                  ∫ _ : Ω, (m x) ^ 2 ∂P) hs₂)
        _ = (∫ ω, (R x ω - m x) ^ 2 ∂P) +
              2 * (m x) * (∫ ω, R x ω - m x ∂P) + (m x) ^ 2 := by
                rw [integral_const_mul, integral_const, probReal_univ, one_smul]
        _ = (∫ ω, (R x ω - m x) ^ 2 ∂P) + (m x) ^ 2 := by
          rw [hD_mean]
          ring
    calc
      ∫ ω, R x ω ^ 2 ∂P =
          (∫ ω, (R x ω - m x) ^ 2 ∂P) + (m x) ^ 2 := hsecond_eq
      _ ≤ v x + (m x) ^ 2 := add_le_add (hvar x hx) le_rfl
  · exact hq_int
  · exact hq_area

/--
Mean and variance area bounds supplied separately imply the integrated second-moment inequality.
-/
theorem expected_area_sq_le_of_separate_mean_variance_areas
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {B : ℝ} (R : ℝ → Ω → ℝ) (m v : ℝ → ℝ)
    (hR_meas : Measurable (fun p : ℝ × Ω => R p.1 p.2))
    (hR_int : ∀ x ∈ Ioc (0 : ℝ) B, Integrable (R x) P)
    (hR_sq_int : ∀ x ∈ Ioc (0 : ℝ) B,
      Integrable (fun ω => R x ω ^ 2) P)
    (hD_sq_int : ∀ x ∈ Ioc (0 : ℝ) B,
      Integrable (fun ω => (R x ω - m x) ^ 2) P)
    (hmean : ∀ x ∈ Ioc (0 : ℝ) B, ∫ ω, R x ω ∂P = m x)
    (hvar : ∀ x ∈ Ioc (0 : ℝ) B,
      ∫ ω, (R x ω - m x) ^ 2 ∂P ≤ v x)
    (hv_nonneg : ∀ x ∈ Ioc (0 : ℝ) B, 0 ≤ v x)
    (hm_meas : Measurable m) (hv_meas : Measurable v)
    (hv_int : IntegrableOn v (Ioc (0 : ℝ) B))
    (hm_sq_int : IntegrableOn (fun x => (m x) ^ 2) (Ioc (0 : ℝ) B))
    {V M : ℝ} (hvar_area : ∫ x : ℝ in Ioc 0 B, v x ≤ V)
    (hmean_area : ∫ x : ℝ in Ioc 0 B, (m x) ^ 2 ≤ M) :
    ∫ ω, ∫ x : ℝ in Ioc 0 B, R x ω ^ 2 ∂volume ∂P ≤ V + M := by
  have hq_int : IntegrableOn (fun x => v x + (m x) ^ 2) (Ioc (0 : ℝ) B) :=
    hv_int.add hm_sq_int
  have hq_area : ∫ x : ℝ in Ioc 0 B, v x + (m x) ^ 2 ≤ V + M := by
    have hsplit :
        ∫ x : ℝ in Ioc 0 B, v x + (m x) ^ 2 =
          (∫ x : ℝ in Ioc 0 B, v x) +
            ∫ x : ℝ in Ioc 0 B, (m x) ^ 2 := by
      have hv_add := integral_add (μ := volume.restrict (Ioc (0 : ℝ) B))
        hv_int.integrable hm_sq_int.integrable
      simpa only [Pi.add_apply] using hv_add
    rw [hsplit]
    exact add_le_add hvar_area hmean_area
  exact expected_area_sq_le_of_mean_variance P R m v hR_meas hR_int hR_sq_int
    hD_sq_int hmean hvar hv_nonneg hm_meas hv_meas hq_int hq_area

end OTSelector
