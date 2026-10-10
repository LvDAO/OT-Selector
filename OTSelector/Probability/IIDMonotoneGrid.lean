import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.L2Space

/-!
# A finite monotone grid for independent sums

A nonnegative sequence is controlled between index-grid anchors by monotonicity. For iid
square-integrable observations, Chebyshev at a fixed number of anchors therefore controls
all prefixes with an error of order the reciprocal of the grid spacing.
-/

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped ENNReal BigOperators

namespace OTSelector.Probability

/-- Cumulative sum in an enumerated family of independent coordinates. -/
def iidPrefix {ι Ω : Type*} (f : Ω → ℝ) (e : ℕ → ι) (n : ℕ) (ω : ι → Ω) : ℝ :=
  ∑ i ∈ Finset.range n, f (ω (e i))

@[fun_prop]
theorem measurable_iidPrefix {ι Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → ℝ} (hf : Measurable f) (e : ℕ → ι) (n : ℕ) :
    Measurable (iidPrefix f e n) := by
  unfold iidPrefix
  fun_prop

theorem iidPrefix_mono {ι Ω : Type*} (f : Ω → ℝ) (e : ℕ → ι) (ω : ι → Ω)
    (h : ∀ i, 0 ≤ f (ω (e i))) : Monotone (fun n ↦ iidPrefix f e n ω) := by
  intro m n hmn
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn) (fun i _ _ ↦ h i)

/-- Monotonicity extends finitely many anchor bounds to every intermediate index. -/
theorem abs_prefix_sub_le_of_grid (S : ℕ → ℝ) (hS : Monotone S)
    {a d : ℝ} (ha : 0 ≤ a) {k M : ℕ} (hk : 0 < k)
    (hgrid : ∀ j ≤ M + 1, |S (j * k) - (j * k : ℕ) * a| ≤ d)
    {n : ℕ} (hn : n ≤ M * k) : |S n - (n : ℝ) * a| ≤ d + k * a := by
  let j := n / k
  have hj : j ≤ M := (Nat.div_le_iff_le_mul_add_pred hk).mpr (by simpa only [Nat.mul_comm k M] using hn.trans (Nat.le_add_right _ _))
  have hlo : j * k ≤ n := Nat.div_mul_le_self n k
  have hhi : n ≤ (j + 1) * k := by simpa only [Nat.mul_comm k, j] using (Nat.lt_mul_div_succ n hk).le
  have hlow := (abs_le.mp (hgrid j (by omega))).1
  have hupp := (abs_le.mp (hgrid (j + 1) (by omega))).2
  have hmono1 := hS hlo
  have hmono2 := hS hhi
  have hlo' : (j * k : ℝ) ≤ n := by exact_mod_cast hlo
  have hhi' : (n : ℝ) ≤ (j + 1) * k := by exact_mod_cast hhi
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hlow hupp
  apply abs_le.mpr
  constructor <;> nlinarith [mul_le_mul_of_nonneg_right hlo' ha,
    mul_le_mul_of_nonneg_right hhi' ha]

/-- Expectation and variance of a finite actual iid prefix. -/
theorem iidPrefix_moments {ι Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Measurable f)
    (h2 : MemLp f 2 μ) {e : ℕ → ι} (he : Injective e) (n : ℕ) :
    (∫ ω, iidPrefix f e n ω ∂Measure.infinitePi (fun _ : ι ↦ μ)) =
        n * (∫ x, f x ∂μ) ∧
    variance (iidPrefix f e n) (Measure.infinitePi (fun _ : ι ↦ μ)) = n * variance f μ := by
  let Q := Measure.infinitePi (fun _ : ι ↦ μ)
  have hrow (i : ℕ) : MemLp (fun ω : ι → Ω ↦ f (ω (e i))) 2 Q :=
    h2.comp_measurePreserving (measurePreserving_eval_infinitePi _ _)
  have hInt (i : ℕ) : Integrable (fun ω : ι → Ω ↦ f (ω (e i))) Q :=
    (hrow i).integrable (by norm_num)
  have hmean (i : ℕ) : (∫ ω : ι → Ω, f (ω (e i)) ∂Q) = ∫ x, f x ∂μ := by
    rw [← Measure.infinitePi_map_eval (fun _ : ι ↦ μ) (e i),
      integral_map (measurable_pi_apply _).aemeasurable hf.aestronglyMeasurable]
  have hvar (i : ℕ) : variance (fun ω : ι → Ω ↦ f (ω (e i))) Q = variance f μ :=
    (measurePreserving_eval_infinitePi _ _).variance_fun_comp hf.aemeasurable
  constructor
  · change (∫ ω : ι → Ω, ∑ i ∈ Finset.range n, f (ω (e i)) ∂Q) = _
    rw [integral_finsetSum _ (fun i _ ↦ hInt i)]
    simp only [hmean, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  · change variance (fun ω ↦ ∑ i ∈ Finset.range n, f (ω (e i))) Q = _
    have hfun : (fun ω : ι → Ω ↦ ∑ i ∈ Finset.range n, f (ω (e i))) =
        ∑ i ∈ Finset.range n, (fun ω : ι → Ω ↦ f (ω (e i))) := by
      ext ω
      simp
    rw [hfun, IndepFun.variance_sum (fun i _ ↦ hrow i)]
    · simp only [hvar, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    · intro i _ j _ hij
      exact (iIndepFun_infinitePi (P := fun _ : ι ↦ μ) (X := fun _ ↦ f)
        (fun _ ↦ hf)).indepFun (he.ne hij)

/-- Chebyshev for a prefix of the concrete infinite product law. -/
theorem iidPrefix_deviation_le {ι Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Measurable f)
    (h2 : MemLp f 2 μ) {e : ℕ → ι} (he : Injective e) (n : ℕ) {d : ℝ} (hd : 0 < d) :
    (Measure.infinitePi (fun _ : ι ↦ μ)).real
      {ω | d ≤ |iidPrefix f e n ω - n * (∫ x, f x ∂μ)|} ≤ n * variance f μ / d ^ 2 := by
  have hs : MemLp (iidPrefix f e n) 2 (Measure.infinitePi (fun _ : ι ↦ μ)) :=
    memLp_finsetSum _ (fun i _ ↦ h2.comp_measurePreserving
      (measurePreserving_eval_infinitePi _ _))
  have h := meas_ge_le_variance_div_sq hs hd
  rw [(iidPrefix_moments μ hf h2 he n).1, (iidPrefix_moments μ hf h2 he n).2] at h
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans_eq
    (ENNReal.toReal_ofReal (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (variance_nonneg f μ))
      (sq_nonneg _)))

/-- A fixed finite set of index-grid anchors has a reciprocal-scale deviation bound. -/
theorem iidPrefix_grid_deviation_le {ι Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Measurable f)
    (h2 : MemLp f 2 μ) {e : ℕ → ι} (he : Injective e) (M k : ℕ)
    {d : ℝ} (hd : 0 < d) :
    (Measure.infinitePi (fun _ : ι ↦ μ)).real
      {ω | ∃ j ≤ M, d ≤ |iidPrefix f e (j * k) ω - (j * k : ℕ) * (∫ x, f x ∂μ)|} ≤
      (M + 1 : ℕ) * ((M * k : ℕ) * variance f μ / d ^ 2) := by
  let Q := Measure.infinitePi (fun _ : ι ↦ μ)
  have hset : {ω | ∃ j ≤ M,
      d ≤ |iidPrefix f e (j * k) ω - (j * k : ℕ) * (∫ x, f x ∂μ)|} =
      ⋃ j ∈ Finset.range (M + 1),
        {ω | d ≤ |iidPrefix f e (j * k) ω - (j * k : ℕ) * (∫ x, f x ∂μ)|} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, Finset.mem_range, Nat.lt_succ_iff]
    aesop
  rw [hset]
  calc
    _ ≤ ∑ j ∈ Finset.range (M + 1), Q.real
        {ω | d ≤ |iidPrefix f e (j * k) ω - (j * k : ℕ) * (∫ x, f x ∂μ)|} :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ Finset.range (M + 1), (M * k : ℕ) * variance f μ / d ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      apply (iidPrefix_deviation_le μ hf h2 he (j * k) hd).trans
      apply div_le_div_of_nonneg_right _ (sq_nonneg d)
      apply mul_le_mul_of_nonneg_right _ (variance_nonneg f μ)
      exact_mod_cast Nat.mul_le_mul_right k (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    _ = _ := by simp [nsmul_eq_mul]

/-- All prefixes up to a linear index horizon are controlled at reciprocal grid-spacing cost. -/
theorem iidPrefix_uniform_deviation_le {ι Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Measurable f)
    (h2 : MemLp f 2 μ) (hf0 : ∀ x, 0 ≤ f x) {e : ℕ → ι} (he : Injective e)
    (M : ℕ) {k : ℕ} (hk : 0 < k) :
    (Measure.infinitePi (fun _ : ι ↦ μ)).real
      {ω | ∃ n ≤ M * k,
        (1 + ∫ x, f x ∂μ) * k < |iidPrefix f e n ω - n * (∫ x, f x ∂μ)|} ≤
      ((M + 2 : ℕ) * (M + 1 : ℕ) * variance f μ) / k := by
  let Q := Measure.infinitePi (fun _ : ι ↦ μ)
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hsubset : {ω | ∃ n ≤ M * k,
      (1 + ∫ x, f x ∂μ) * k < |iidPrefix f e n ω - n * (∫ x, f x ∂μ)|} ⊆
      {ω | ∃ j ≤ M + 1,
        (k : ℝ) ≤ |iidPrefix f e (j * k) ω - (j * k : ℕ) * (∫ x, f x ∂μ)|} := by
    intro ω hω
    by_contra hbad
    have hgood : ∀ j ≤ M + 1,
        |iidPrefix f e (j * k) ω - (j * k : ℕ) * (∫ x, f x ∂μ)| ≤ k := by
      intro j hj
      exact (lt_of_not_ge fun h ↦ hbad ⟨j, hj, h⟩).le
    rcases hω with ⟨n, hn, hdev⟩
    have hbound := abs_prefix_sub_le_of_grid (fun n ↦ iidPrefix f e n ω)
      (iidPrefix_mono f e ω (fun i ↦ hf0 _)) (integral_nonneg hf0) hk hgood hn
    nlinarith
  apply (measureReal_mono hsubset).trans
  apply (iidPrefix_grid_deviation_le μ hf h2 he (M + 1) k hk').trans_eq
  push_cast
  field_simp
  ring

end OTSelector.Probability
