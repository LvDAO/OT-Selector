import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Moments.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Initial current: finite binomial input bounds

This file records the finite-dimensional probability facts used at the beginning of the
feedback argument.  The law is written with mathlib's genuine binomial measure
`ProbabilityTheory.Bin(ℝ, n, p)`; no witness or interface is introduced here.

The first theorem is the exact binomial MGF formula.  The second one is the elementary
product-law upper bound for the absolute difference.  A centred third-moment layer is
kept in a form that can be instantiated by a separate moment calculation without
pretending that `HasLaw` itself supplies a variance theorem.
-/

namespace OTSelector.Feedback

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory unitInterval BigOperators

/-! ## Exact one-binomial MGF -/

private lemma integral_exp_mul_binomial (n : ℕ) (p : I) (θ : ℝ) :
    ∫ x : ℝ, Real.exp (θ * x) ∂Bin(ℝ, n, p) =
      (1 - (p : ℝ) + (p : ℝ) * Real.exp θ) ^ n := by
  rw [ProbabilityTheory.integral_map_cast_binomial]
  rw [← n.range_succ_eq_Iic]
  have hpow := (add_pow ((p : ℝ) * Real.exp θ) (1 - (p : ℝ)) n).symm
  calc
    ∑ k ∈ Finset.range (n + 1),
        ((n.choose k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k)) •
          Real.exp (θ * (k : ℝ)) =
        ∑ k ∈ Finset.range (n + 1),
          ((p : ℝ) * Real.exp θ) ^ k * (1 - (p : ℝ)) ^ (n - k) *
            (n.choose k : ℝ) := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [smul_eq_mul]
      rw [show θ * (k : ℝ) = (k : ℝ) * θ by ring, Real.exp_nat_mul]
      rw [mul_pow]
      ring
    _ = ((p : ℝ) * Real.exp θ + (1 - (p : ℝ))) ^ n := hpow
    _ = (1 - (p : ℝ) + (p : ℝ) * Real.exp θ) ^ n := by ring_nf

/-- Exact MGF of a real-valued binomial law. -/
theorem mgf_binomial (n : ℕ) (p : I) (θ : ℝ) :
    ProbabilityTheory.mgf (id : ℝ → ℝ) Bin(ℝ, n, p) θ =
      (1 - (p : ℝ) + (p : ℝ) * Real.exp θ) ^ n := by
  simpa [ProbabilityTheory.mgf, id_eq] using integral_exp_mul_binomial n p θ

/-! ## Product-law absolute-difference MGF -/

private lemma ae_nonneg_binomial (n : ℕ) (p : I) :
    ∀ᵐ x : ℝ ∂Bin(ℝ, n, p), 0 ≤ x := by
  rw [show Bin(ℝ, n, p) = Measure.map (Nat.cast : ℕ → ℝ) Bin(n, p) by rfl]
  apply (ae_map_iff (by fun_prop) measurableSet_Ici).2
  exact ae_of_all _ (fun k => by positivity)

private lemma ae_le_binomial (n : ℕ) (p : I) :
    ∀ᵐ x : ℝ ∂Bin(ℝ, n, p), x ≤ n := by
  rw [show Bin(ℝ, n, p) = Measure.map (Nat.cast : ℕ → ℝ) Bin(n, p) by rfl]
  apply (ae_map_iff (by fun_prop) measurableSet_Iic).2
  simpa using
    (ae_le_of_hasLaw_binomial
      (HasLaw.id : HasLaw (id : ℕ → ℕ) Bin(n, p) Bin(n, p)))

private lemma integrable_binomial_difference_pow (n : ℕ) (p : I) (k : ℕ) :
    Integrable (fun z : ℝ × ℝ => |z.1 - z.2| ^ k)
      ((Bin(ℝ, n, p)).prod Bin(ℝ, n, p)) := by
  have hprod : ∀ᵐ z : ℝ × ℝ ∂(Bin(ℝ, n, p)).prod Bin(ℝ, n, p),
      0 ≤ z.1 ∧ z.1 ≤ n ∧ 0 ≤ z.2 ∧ z.2 ≤ n := by
    have hs : MeasurableSet {z : ℝ × ℝ | 0 ≤ z.1 ∧ z.1 ≤ n ∧ 0 ≤ z.2 ∧ z.2 ≤ n} := by
      exact (measurableSet_Ici.preimage measurable_fst).inter
        ((measurableSet_Iic.preimage measurable_fst).inter
          ((measurableSet_Ici.preimage measurable_snd).inter
            (measurableSet_Iic.preimage measurable_snd)))
    rw [Measure.ae_prod_iff_ae_ae hs]
    filter_upwards [ae_nonneg_binomial n p, ae_le_binomial n p] with x hx0 hxN
    filter_upwards [ae_nonneg_binomial n p, ae_le_binomial n p] with y hy0 hyN
    exact ⟨hx0, hxN, hy0, hyN⟩
  refine Integrable.mono' (g := fun _ : ℝ × ℝ => (2 * (n : ℝ)) ^ k)
    (integrable_const _) (by fun_prop) (hprod.mono fun z hz => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
  have habs : |z.1 - z.2| ≤ 2 * (n : ℝ) := by
    rw [abs_sub_le_iff]
    constructor <;> linarith [hz.1, hz.2.1, hz.2.2.1, hz.2.2.2]
  exact pow_le_pow_left₀ (abs_nonneg _) habs k

private lemma exp_abs_sub_le_exp_add (θ x y : ℝ) (hθ : 0 ≤ θ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.exp (θ * |x - y|) ≤ Real.exp (θ * (x + y)) + Real.exp (θ * (y + x)) := by
  have habs : |x - y| ≤ x + y := by
    rw [abs_sub_le_iff]
    constructor <;> linarith
  have hmain : Real.exp (θ * |x - y|) ≤ Real.exp (θ * (x + y)) := by
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left habs hθ)
  exact hmain.trans (le_add_of_nonneg_right (Real.exp_nonneg _))

/--
For two independent `Bin(n,p)` coordinates, the exponential MGF of their absolute
difference is bounded by the product-law expression.  The final exponential form is
often more convenient in the sparse regime `λ = n p`.
-/
theorem integral_exp_abs_sub_binomial_prod_le (n : ℕ) (p : I) (θ : ℝ) (hθ : 0 ≤ θ) :
    ∫ z : ℝ × ℝ, Real.exp (θ * |z.1 - z.2|)
        ∂(Bin(ℝ, n, p)).prod Bin(ℝ, n, p) ≤
      2 * (1 - (p : ℝ) + (p : ℝ) * Real.exp θ) ^ (2 * n) := by
  have h₁ : Integrable (fun z : ℝ × ℝ => Real.exp (θ * (z.1 + z.2)))
      ((Bin(ℝ, n, p)).prod Bin(ℝ, n, p)) := by
    have heq : (fun z : ℝ × ℝ => Real.exp (θ * (z.1 + z.2))) =
        (fun z : ℝ × ℝ => Real.exp (θ * z.1) * Real.exp (θ * z.2)) := by
      funext z
      rw [mul_add, Real.exp_add]
    rw [heq]
    have hf : Integrable (fun x : ℝ => Real.exp (θ * x)) (Bin(ℝ, n, p)) :=
      ProbabilityTheory.integrable_map_cast_binomial _
    exact hf.mul_prod hf
  have h₂ : Integrable (fun z : ℝ × ℝ => Real.exp (θ * (z.2 + z.1)))
      ((Bin(ℝ, n, p)).prod Bin(ℝ, n, p)) := by
    simpa [add_comm] using h₁
  have hprod : ∀ᵐ z : ℝ × ℝ ∂(Bin(ℝ, n, p)).prod Bin(ℝ, n, p),
      0 ≤ z.1 ∧ 0 ≤ z.2 := by
    have hs : MeasurableSet {z : ℝ × ℝ | 0 ≤ z.1 ∧ 0 ≤ z.2} := by
      exact (measurableSet_Ici.preimage measurable_fst).inter
        (measurableSet_Ici.preimage measurable_snd)
    rw [Measure.ae_prod_iff_ae_ae hs]
    filter_upwards [ae_nonneg_binomial n p] with x hx
    filter_upwards [ae_nonneg_binomial n p] with y hy
    exact ⟨hx, hy⟩
  have h_int : Integrable (fun z : ℝ × ℝ => Real.exp (θ * |z.1 - z.2|))
      ((Bin(ℝ, n, p)).prod Bin(ℝ, n, p)) := by
    exact MeasureTheory.Integrable.mono' (MeasureTheory.Integrable.add h₁ h₂) (by fun_prop)
      (hprod.mono fun z hz => by
        simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
          exp_abs_sub_le_exp_add θ z.1 z.2 hθ hz.1 hz.2)
  calc
    ∫ z : ℝ × ℝ, Real.exp (θ * |z.1 - z.2|)
          ∂(Bin(ℝ, n, p)).prod Bin(ℝ, n, p) ≤
        ∫ z : ℝ × ℝ, (Real.exp (θ * (z.1 + z.2)) +
          Real.exp (θ * (z.2 + z.1))) ∂(Bin(ℝ, n, p)).prod Bin(ℝ, n, p) :=
      integral_mono_ae h_int (MeasureTheory.Integrable.add h₁ h₂)
        (hprod.mono fun z hz => exp_abs_sub_le_exp_add θ z.1 z.2 hθ hz.1 hz.2)
    _ = 2 * (1 - (p : ℝ) + (p : ℝ) * Real.exp θ) ^ (2 * n) := by
      rw [integral_add h₁ h₂]
      rw [show (fun z : ℝ × ℝ => Real.exp (θ * (z.1 + z.2))) =
          (fun z : ℝ × ℝ => Real.exp (θ * z.1) * Real.exp (θ * z.2)) by
            funext z; rw [mul_add, Real.exp_add]]
      rw [show (fun z : ℝ × ℝ => Real.exp (θ * (z.2 + z.1))) =
          (fun z : ℝ × ℝ => Real.exp (θ * z.2) * Real.exp (θ * z.1)) by
            funext z; rw [mul_add, Real.exp_add]]
      have hprod₁ := integral_prod_mul
        (μ := Bin(ℝ, n, p)) (ν := Bin(ℝ, n, p))
        (fun x : ℝ => Real.exp (θ * x)) (fun y : ℝ => Real.exp (θ * y))
      have hprod₂ :
          ∫ z : ℝ × ℝ, Real.exp (θ * z.2) * Real.exp (θ * z.1)
              ∂(Bin(ℝ, n, p)).prod Bin(ℝ, n, p) =
            (∫ x : ℝ, Real.exp (θ * x) ∂Bin(ℝ, n, p)) *
              ∫ y : ℝ, Real.exp (θ * y) ∂Bin(ℝ, n, p) := by
        simpa [mul_comm] using hprod₁
      rw [hprod₁, hprod₂]
      rw [integral_exp_mul_binomial]
      ring_nf

/-! ## Explicit finite binomial moments -/

private def binomial_weight (n k : ℕ) (p : I) : ℝ :=
  (n.choose k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k)

private lemma factorial_moment_sum (n r : ℕ) (p : I) (hr : r ≤ n) :
    ∑ k ∈ Finset.range (n + 1),
      (k.descFactorial r : ℝ) * binomial_weight n k p =
      (n.descFactorial r : ℝ) * (p : ℝ) ^ r := by
  have hrr : r ≤ n + 1 := le_trans hr (Nat.le_succ n)
  rw [← Finset.sum_range_add_sum_Ico
    (fun k => (k.descFactorial r : ℝ) * binomial_weight n k p) hrr]
  have hfirst : ∑ k ∈ Finset.range r,
      (k.descFactorial r : ℝ) * binomial_weight n k p = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hkr : k < r := Finset.mem_range.mp hk
    rw [Nat.descFactorial_of_lt hkr]
    simp
  rw [hfirst, zero_add, Finset.sum_Ico_eq_sum_range]
  have hnr : n - r + 1 = n + 1 - r := by omega
  rw [← hnr]
  have hsum : ∑ j ∈ Finset.range (n - r + 1),
      (r + j).descFactorial r * binomial_weight n (r + j) p =
      (n.descFactorial r : ℝ) * (p : ℝ) ^ r := by
    calc
      ∑ j ∈ Finset.range (n - r + 1),
          (r + j).descFactorial r * binomial_weight n (r + j) p =
          ∑ j ∈ Finset.range (n - r + 1),
            ((n.descFactorial r : ℝ) * (p : ℝ) ^ r) *
              ((n - r).choose j : ℝ) * (p : ℝ) ^ j *
                (1 - (p : ℝ)) ^ ((n - r) - j) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hj' : j ≤ n - r := by
          exact Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        have hkj : r ≤ r + j := by omega
        have hsub : n - (r + j) = (n - r) - j := by omega
        have hchoose : (n.choose (r + j) : ℝ) * ((r + j).choose r : ℝ) =
            (n.choose r : ℝ) * ((n - r).choose j : ℝ) := by
          norm_cast
          rw [Nat.choose_mul hkj]
          simp
        calc
          (r + j).descFactorial r * binomial_weight n (r + j) p =
              (r.factorial : ℝ) * ((r + j).choose r : ℝ) *
                (n.choose (r + j) : ℝ) * (p : ℝ) ^ (r + j) *
                  (1 - (p : ℝ)) ^ (n - (r + j)) := by
            simp [binomial_weight, Nat.descFactorial_eq_factorial_mul_choose]
            ring
          _ = ((n.descFactorial r : ℝ) * (p : ℝ) ^ r) *
              ((n - r).choose j : ℝ) * (p : ℝ) ^ j *
                (1 - (p : ℝ)) ^ ((n - r) - j) := by
            rw [hsub, pow_add]
            calc
              (r.factorial : ℝ) * ((r + j).choose r : ℝ) *
                  (n.choose (r + j) : ℝ) * ((p : ℝ) ^ r * (p : ℝ) ^ j) *
                    (1 - (p : ℝ)) ^ (n - r - j) =
                  (r.factorial : ℝ) *
                    (((r + j).choose r : ℝ) * (n.choose (r + j) : ℝ)) *
                    ((p : ℝ) ^ r * (p : ℝ) ^ j) *
                      (1 - (p : ℝ)) ^ (n - r - j) := by ring
              _ = (r.factorial : ℝ) *
                    ((n.choose r : ℝ) * ((n - r).choose j : ℝ)) *
                    ((p : ℝ) ^ r * (p : ℝ) ^ j) *
                      (1 - (p : ℝ)) ^ (n - r - j) := by
                rw [show ((r + j).choose r : ℝ) * (n.choose (r + j) : ℝ) =
                  (n.choose r : ℝ) * ((n - r).choose j : ℝ) by
                    rw [mul_comm, hchoose]]
              _ = ((n.descFactorial r : ℝ) * (p : ℝ) ^ r) *
                    ((n - r).choose j : ℝ) * (p : ℝ) ^ j *
                      (1 - (p : ℝ)) ^ (n - r - j) := by
                rw [Nat.descFactorial_eq_factorial_mul_choose]
                push_cast
                ring
      _ = (n.descFactorial r : ℝ) * (p : ℝ) ^ r := by
        calc
          ∑ j ∈ Finset.range (n - r + 1),
              ((n.descFactorial r : ℝ) * (p : ℝ) ^ r) *
                ((n - r).choose j : ℝ) * (p : ℝ) ^ j *
                  (1 - (p : ℝ)) ^ ((n - r) - j) =
              ((n.descFactorial r : ℝ) * (p : ℝ) ^ r) *
                ∑ j ∈ Finset.range (n - r + 1),
                  ((n - r).choose j : ℝ) * (p : ℝ) ^ j *
                    (1 - (p : ℝ)) ^ ((n - r) - j) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            ring
          _ = (n.descFactorial r : ℝ) * (p : ℝ) ^ r := by
            have hpq := add_pow (p : ℝ) (1 - (p : ℝ)) (n - r)
            calc
              (n.descFactorial r : ℝ) * (p : ℝ) ^ r *
                  ∑ j ∈ Finset.range (n - r + 1),
                    ((n - r).choose j : ℝ) * (p : ℝ) ^ j *
                      (1 - (p : ℝ)) ^ ((n - r) - j) =
                  (n.descFactorial r : ℝ) * (p : ℝ) ^ r *
                    ∑ j ∈ Finset.range (n - r + 1),
                      (p : ℝ) ^ j * (1 - (p : ℝ)) ^ ((n - r) - j) *
                        ((n - r).choose j : ℝ) := by
                congr 1
                apply Finset.sum_congr rfl
                intro j hj
                ring
              _ = (n.descFactorial r : ℝ) * (p : ℝ) ^ r *
                  ((p : ℝ) + (1 - (p : ℝ))) ^ (n - r) := by
                rw [hpq]
              _ = (n.descFactorial r : ℝ) * (p : ℝ) ^ r := by
                ring_nf
  exact hsum

private lemma integral_binomial_pow (n : ℕ) (p : I) (r : ℕ) :
    ∫ x : ℝ, x ^ r ∂Bin(ℝ, n, p) =
      ∑ k ∈ Finset.range (n + 1), binomial_weight n k p * (k : ℝ) ^ r := by
  rw [ProbabilityTheory.integral_map_cast_binomial]
  rw [← n.range_succ_eq_Iic]
  simp only [smul_eq_mul]
  rfl

private lemma factorial_moment_sum_all (n r : ℕ) (p : I) :
    ∑ k ∈ Finset.range (n + 1),
      (k.descFactorial r : ℝ) * binomial_weight n k p =
      (n.descFactorial r : ℝ) * (p : ℝ) ^ r := by
  by_cases h : r ≤ n
  · exact factorial_moment_sum n r p h
  · have hnr : n < r := Nat.lt_of_not_ge h
    have hsum : ∑ k ∈ Finset.range (n + 1),
        (k.descFactorial r : ℝ) * binomial_weight n k p = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hkn : k < r := hk_le.trans_lt hnr
      rw [Nat.descFactorial_of_lt hkn]
      simp
    rw [hsum, Nat.descFactorial_of_lt hnr]
    simp

private lemma binomial_desc_id2 (k : ℕ) :
    (k : ℝ)^2 = (k.descFactorial 2 : ℝ) + (k.descFactorial 1 : ℝ) := by
  rw [Nat.cast_descFactorial_two]
  simp
  ring

private lemma binomial_raw_second (n : ℕ) (p : I) :
    ∫ x : ℝ, x ^ 2 ∂Bin(ℝ, n, p) =
      (n.descFactorial 2 : ℝ) * (p : ℝ) ^ 2 +
        (n.descFactorial 1 : ℝ) * (p : ℝ) := by
  rw [integral_binomial_pow]
  calc
    ∑ k ∈ Finset.range (n + 1), binomial_weight n k p * (k : ℝ) ^ 2 =
        ∑ k ∈ Finset.range (n + 1),
          binomial_weight n k p *
            ((k.descFactorial 2 : ℝ) + (k.descFactorial 1 : ℝ)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [binomial_desc_id2]
    _ = ∑ k ∈ Finset.range (n + 1),
          (binomial_weight n k p * (k.descFactorial 2 : ℝ) +
            binomial_weight n k p * (k.descFactorial 1 : ℝ)) := by
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = (∑ k ∈ Finset.range (n + 1),
          binomial_weight n k p * (k.descFactorial 2 : ℝ)) +
          ∑ k ∈ Finset.range (n + 1),
            binomial_weight n k p * (k.descFactorial 1 : ℝ) := by
      rw [Finset.sum_add_distrib]
    _ = (n.descFactorial 2 : ℝ) * (p : ℝ)^2 +
          (n.descFactorial 1 : ℝ) * (p : ℝ) := by
      rw [show (∑ k ∈ Finset.range (n + 1),
          binomial_weight n k p * (k.descFactorial 2 : ℝ)) =
          ∑ k ∈ Finset.range (n + 1),
            (k.descFactorial 2 : ℝ) * binomial_weight n k p by
            apply Finset.sum_congr rfl; intro k hk; ring,
        show (∑ k ∈ Finset.range (n + 1),
          binomial_weight n k p * (k.descFactorial 1 : ℝ)) =
          ∑ k ∈ Finset.range (n + 1),
            (k.descFactorial 1 : ℝ) * binomial_weight n k p by
            apply Finset.sum_congr rfl; intro k hk; ring]
      rw [factorial_moment_sum_all n 2 p, factorial_moment_sum_all n 1 p]
      simp [pow_one]

private lemma binomial_desc_id3 (k : ℕ) :
    (k : ℝ)^3 = (k.descFactorial 3 : ℝ) + 3 * (k.descFactorial 2 : ℝ) +
      (k.descFactorial 1 : ℝ) := by
  have h2 : (k : ℝ)^2 = (k.descFactorial 2 : ℝ) + (k.descFactorial 1 : ℝ) := by
    rw [Nat.cast_descFactorial_two]
    simp
    ring
  have hrec2 : (k.descFactorial 2 : ℝ) * (k : ℝ) =
      (k.descFactorial 3 : ℝ) + 2 * (k.descFactorial 2 : ℝ) := by
    have h := Nat.descFactorial_mul_self k 2
    convert congrArg (fun z : ℕ => (z : ℝ)) h using 1 <;> norm_num
  have hrec1 : (k : ℝ) * (k : ℝ) =
      (k.descFactorial 2 : ℝ) + (k : ℝ) := by
    have h := Nat.descFactorial_mul_self k 1
    convert congrArg (fun z : ℕ => (z : ℝ)) h using 1 <;> norm_num
  calc
    (k : ℝ)^3 = (k : ℝ) * (k : ℝ)^2 := by ring
    _ = (k : ℝ) * ((k.descFactorial 2 : ℝ) + (k.descFactorial 1 : ℝ)) := by
      rw [h2]
    _ = (k : ℝ) * (k.descFactorial 2 : ℝ) +
        (k : ℝ) * (k.descFactorial 1 : ℝ) := by ring
    _ = (k.descFactorial 3 : ℝ) + 2 * (k.descFactorial 2 : ℝ) +
        ((k.descFactorial 2 : ℝ) + (k : ℝ)) := by
      rw [show (k : ℝ) * (k.descFactorial 2 : ℝ) =
          (k.descFactorial 2 : ℝ) * (k : ℝ) by ring, hrec2,
        show (k : ℝ) * (k.descFactorial 1 : ℝ) =
          (k : ℝ) * (k : ℝ) by rw [Nat.descFactorial_one], hrec1]
    _ = (k.descFactorial 3 : ℝ) + 3 * (k.descFactorial 2 : ℝ) +
        (k.descFactorial 1 : ℝ) := by
      rw [Nat.descFactorial_one]
      ring

private lemma binomial_raw_third (n : ℕ) (p : I) :
    ∫ x : ℝ, x ^ 3 ∂Bin(ℝ, n, p) =
      (n.descFactorial 3 : ℝ) * (p : ℝ) ^ 3 +
        3 * (n.descFactorial 2 : ℝ) * (p : ℝ) ^ 2 +
        (n.descFactorial 1 : ℝ) * (p : ℝ) := by
  rw [integral_binomial_pow]
  calc
    ∑ k ∈ Finset.range (n + 1), binomial_weight n k p * (k : ℝ) ^ 3 =
        ∑ k ∈ Finset.range (n + 1), binomial_weight n k p *
          ((k.descFactorial 3 : ℝ) + 3 * (k.descFactorial 2 : ℝ) +
            (k.descFactorial 1 : ℝ)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [binomial_desc_id3]
    _ = (∑ k ∈ Finset.range (n + 1),
          binomial_weight n k p * (k.descFactorial 3 : ℝ)) +
        3 * (∑ k ∈ Finset.range (n + 1),
          binomial_weight n k p * (k.descFactorial 2 : ℝ)) +
        ∑ k ∈ Finset.range (n + 1),
          binomial_weight n k p * (k.descFactorial 1 : ℝ) := by
      calc
        ∑ k ∈ Finset.range (n + 1), binomial_weight n k p *
            ((k.descFactorial 3 : ℝ) + 3 * (k.descFactorial 2 : ℝ) +
              (k.descFactorial 1 : ℝ)) =
            ∑ k ∈ Finset.range (n + 1),
              (binomial_weight n k p * (k.descFactorial 3 : ℝ) +
                3 * (binomial_weight n k p * (k.descFactorial 2 : ℝ)) +
                binomial_weight n k p * (k.descFactorial 1 : ℝ)) := by
          apply Finset.sum_congr rfl
          intro k hk
          ring
        _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = (n.descFactorial 3 : ℝ) * (p : ℝ) ^ 3 +
        3 * (n.descFactorial 2 : ℝ) * (p : ℝ) ^ 2 +
        (n.descFactorial 1 : ℝ) * (p : ℝ) := by
      rw [show (∑ k ∈ Finset.range (n + 1),
          binomial_weight n k p * (k.descFactorial 3 : ℝ)) =
          ∑ k ∈ Finset.range (n + 1),
            (k.descFactorial 3 : ℝ) * binomial_weight n k p by
            apply Finset.sum_congr rfl; intro k hk; ring,
        show (∑ k ∈ Finset.range (n + 1),
          binomial_weight n k p * (k.descFactorial 2 : ℝ)) =
          ∑ k ∈ Finset.range (n + 1),
            (k.descFactorial 2 : ℝ) * binomial_weight n k p by
            apply Finset.sum_congr rfl; intro k hk; ring,
        show (∑ k ∈ Finset.range (n + 1),
          binomial_weight n k p * (k.descFactorial 1 : ℝ)) =
          ∑ k ∈ Finset.range (n + 1),
            (k.descFactorial 1 : ℝ) * binomial_weight n k p by
            apply Finset.sum_congr rfl; intro k hk; ring,
        factorial_moment_sum_all n 3 p, factorial_moment_sum_all n 2 p,
        factorial_moment_sum_all n 1 p]
      ring

private lemma binomial_desc_id4 (k : ℕ) :
    (k : ℝ)^4 = (k.descFactorial 4 : ℝ) + 6 * (k.descFactorial 3 : ℝ) +
      7 * (k.descFactorial 2 : ℝ) + (k.descFactorial 1 : ℝ) := by
  have h2 : (k : ℝ)^2 = (k.descFactorial 2 : ℝ) + (k.descFactorial 1 : ℝ) := by
    rw [Nat.cast_descFactorial_two]
    simp
    ring
  have h3 : (k : ℝ)^3 = (k.descFactorial 3 : ℝ) +
      3 * (k.descFactorial 2 : ℝ) + (k : ℝ) := by
    have h2' := h2
    rw [Nat.descFactorial_one] at h2'
    have hrec2 : (k.descFactorial 2 : ℝ) * (k : ℝ) =
        (k.descFactorial 3 : ℝ) + 2 * (k.descFactorial 2 : ℝ) := by
      have h := Nat.descFactorial_mul_self k 2
      convert congrArg (fun z : ℕ => (z : ℝ)) h using 1 <;> norm_num
    have hrec1 : (k : ℝ) * (k : ℝ) =
        (k.descFactorial 2 : ℝ) + (k : ℝ) := by
      have h := Nat.descFactorial_mul_self k 1
      convert congrArg (fun z : ℕ => (z : ℝ)) h using 1 <;> norm_num
    calc
      (k : ℝ)^3 = (k : ℝ) * (k : ℝ)^2 := by ring
      _ = (k : ℝ) * ((k.descFactorial 2 : ℝ) + (k : ℝ)) := by rw [h2']
      _ = (k : ℝ) * (k.descFactorial 2 : ℝ) +
          (k : ℝ) * (k : ℝ) := by ring
      _ = (k.descFactorial 3 : ℝ) + 2 * (k.descFactorial 2 : ℝ) +
          ((k.descFactorial 2 : ℝ) + (k : ℝ)) := by
        rw [show (k : ℝ) * (k.descFactorial 2 : ℝ) =
            (k.descFactorial 2 : ℝ) * (k : ℝ) by ring, hrec2, hrec1]
      _ = (k.descFactorial 3 : ℝ) + 3 * (k.descFactorial 2 : ℝ) +
          (k : ℝ) := by ring
  have hrec3 : (k.descFactorial 3 : ℝ) * (k : ℝ) =
      (k.descFactorial 4 : ℝ) + 3 * (k.descFactorial 3 : ℝ) := by
    have h := Nat.descFactorial_mul_self k 3
    convert congrArg (fun z : ℕ => (z : ℝ)) h using 1 <;> norm_num
  have hrec2 : (k.descFactorial 2 : ℝ) * (k : ℝ) =
      (k.descFactorial 3 : ℝ) + 2 * (k.descFactorial 2 : ℝ) := by
    have h := Nat.descFactorial_mul_self k 2
    convert congrArg (fun z : ℕ => (z : ℝ)) h using 1 <;> norm_num
  have hrec1 : (k : ℝ) * (k : ℝ) =
      (k.descFactorial 2 : ℝ) + (k : ℝ) := by
    have h := Nat.descFactorial_mul_self k 1
    convert congrArg (fun z : ℕ => (z : ℝ)) h using 1 <;> norm_num
  calc
    (k : ℝ)^4 = (k : ℝ) * (k : ℝ)^3 := by ring
    _ = (k : ℝ) * ((k.descFactorial 3 : ℝ) +
        3 * (k.descFactorial 2 : ℝ) + (k : ℝ)) := by rw [h3]
    _ = (k : ℝ) * (k.descFactorial 3 : ℝ) +
        3 * ((k : ℝ) * (k.descFactorial 2 : ℝ)) +
        (k : ℝ) * (k : ℝ) := by ring
    _ = (k.descFactorial 4 : ℝ) + 3 * (k.descFactorial 3 : ℝ) +
        3 * ((k.descFactorial 3 : ℝ) + 2 * (k.descFactorial 2 : ℝ)) +
        ((k.descFactorial 2 : ℝ) + (k : ℝ)) := by
      rw [show (k : ℝ) * (k.descFactorial 3 : ℝ) =
            (k.descFactorial 3 : ℝ) * (k : ℝ) by ring, hrec3,
        show (k : ℝ) * (k.descFactorial 2 : ℝ) =
            (k.descFactorial 2 : ℝ) * (k : ℝ) by ring, hrec2, hrec1]
    _ = (k.descFactorial 4 : ℝ) + 6 * (k.descFactorial 3 : ℝ) +
        7 * (k.descFactorial 2 : ℝ) + (k : ℝ) := by ring
    _ = (k.descFactorial 4 : ℝ) + 6 * (k.descFactorial 3 : ℝ) +
        7 * (k.descFactorial 2 : ℝ) + (k.descFactorial 1 : ℝ) := by
      rw [Nat.descFactorial_one]

private lemma binomial_raw_fourth (n : ℕ) (p : I) :
    ∫ x : ℝ, x ^ 4 ∂Bin(ℝ, n, p) =
      (n.descFactorial 4 : ℝ) * (p : ℝ) ^ 4 +
        6 * (n.descFactorial 3 : ℝ) * (p : ℝ) ^ 3 +
        7 * (n.descFactorial 2 : ℝ) * (p : ℝ) ^ 2 +
        (n.descFactorial 1 : ℝ) * (p : ℝ) := by
  rw [integral_binomial_pow]
  calc
    ∑ k ∈ Finset.range (n + 1), binomial_weight n k p * (k : ℝ) ^ 4 =
        ∑ k ∈ Finset.range (n + 1), binomial_weight n k p *
          ((k.descFactorial 4 : ℝ) + 6 * (k.descFactorial 3 : ℝ) +
            7 * (k.descFactorial 2 : ℝ) + (k.descFactorial 1 : ℝ)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [binomial_desc_id4]
    _ = (∑ k ∈ Finset.range (n + 1),
          binomial_weight n k p * (k.descFactorial 4 : ℝ)) +
        6 * (∑ k ∈ Finset.range (n + 1),
          binomial_weight n k p * (k.descFactorial 3 : ℝ)) +
        7 * (∑ k ∈ Finset.range (n + 1),
          binomial_weight n k p * (k.descFactorial 2 : ℝ)) +
        ∑ k ∈ Finset.range (n + 1),
          binomial_weight n k p * (k.descFactorial 1 : ℝ) := by
      calc
        ∑ k ∈ Finset.range (n + 1), binomial_weight n k p *
            ((k.descFactorial 4 : ℝ) + 6 * (k.descFactorial 3 : ℝ) +
              7 * (k.descFactorial 2 : ℝ) + (k.descFactorial 1 : ℝ)) =
            ∑ k ∈ Finset.range (n + 1),
              (binomial_weight n k p * (k.descFactorial 4 : ℝ) +
                6 * (binomial_weight n k p * (k.descFactorial 3 : ℝ)) +
                7 * (binomial_weight n k p * (k.descFactorial 2 : ℝ)) +
                binomial_weight n k p * (k.descFactorial 1 : ℝ)) := by
          apply Finset.sum_congr rfl
          intro k hk
          ring
        _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
            Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = (n.descFactorial 4 : ℝ) * (p : ℝ) ^ 4 +
        6 * (n.descFactorial 3 : ℝ) * (p : ℝ) ^ 3 +
        7 * (n.descFactorial 2 : ℝ) * (p : ℝ) ^ 2 +
        (n.descFactorial 1 : ℝ) * (p : ℝ) := by
      rw [show (∑ k ∈ Finset.range (n + 1),
          binomial_weight n k p * (k.descFactorial 4 : ℝ)) =
          ∑ k ∈ Finset.range (n + 1),
            (k.descFactorial 4 : ℝ) * binomial_weight n k p by
            apply Finset.sum_congr rfl; intro k hk; ring,
        show (∑ k ∈ Finset.range (n + 1),
          binomial_weight n k p * (k.descFactorial 3 : ℝ)) =
          ∑ k ∈ Finset.range (n + 1),
            (k.descFactorial 3 : ℝ) * binomial_weight n k p by
            apply Finset.sum_congr rfl; intro k hk; ring,
        show (∑ k ∈ Finset.range (n + 1),
          binomial_weight n k p * (k.descFactorial 2 : ℝ)) =
          ∑ k ∈ Finset.range (n + 1),
            (k.descFactorial 2 : ℝ) * binomial_weight n k p by
            apply Finset.sum_congr rfl; intro k hk; ring,
        show (∑ k ∈ Finset.range (n + 1),
          binomial_weight n k p * (k.descFactorial 1 : ℝ)) =
          ∑ k ∈ Finset.range (n + 1),
            (k.descFactorial 1 : ℝ) * binomial_weight n k p by
            apply Finset.sum_congr rfl; intro k hk; ring,
        factorial_moment_sum_all n 4 p, factorial_moment_sum_all n 3 p,
        factorial_moment_sum_all n 2 p, factorial_moment_sum_all n 1 p]
      ring

/-! ## Exact moments of the independent difference -/

private lemma binomial_difference_second (n : ℕ) (p : I) :
    ∫ z : ℝ × ℝ, (z.1 - z.2) ^ 2
        ∂(Bin(ℝ, n, p)).prod Bin(ℝ, n, p) =
      2 * (n : ℝ) * (p : ℝ) * (1 - (p : ℝ)) := by
  let μ : Measure ℝ := Bin(ℝ, n, p)
  have hpow (r : ℕ) : Integrable (fun x : ℝ => x ^ r) μ := by
    simpa [μ] using (ProbabilityTheory.integrable_map_cast_binomial
      (n := n) (p := p) (fun x : ℝ => x ^ r))
  have h20 : Integrable (fun z : ℝ × ℝ => z.1 ^ 2 * (1 : ℝ)) (μ.prod μ) :=
    (hpow 2).mul_prod (integrable_const (1 : ℝ))
  have h02 : Integrable (fun z : ℝ × ℝ => (1 : ℝ) * z.2 ^ 2) (μ.prod μ) :=
    (integrable_const (1 : ℝ)).mul_prod (hpow 2)
  have h11 : Integrable (fun z : ℝ × ℝ => z.1 ^ 1 * z.2 ^ 1) (μ.prod μ) :=
    (hpow 1).mul_prod (hpow 1)
  have h20' : Integrable (fun z : ℝ × ℝ => z.1 ^ 2) (μ.prod μ) := by simpa using h20
  have h02' : Integrable (fun z : ℝ × ℝ => z.2 ^ 2) (μ.prod μ) := by simpa using h02
  have h11' : Integrable (fun z : ℝ × ℝ => z.1 * z.2) (μ.prod μ) := by simpa using h11
  have hsum : Integrable (fun z : ℝ × ℝ => z.1 ^ 2 + z.2 ^ 2) (μ.prod μ) :=
    h20'.add h02'
  have hsum' : Integrable
      (fun z : ℝ × ℝ => z.1 ^ 2 + z.2 ^ 2 - 2 * (z.1 * z.2)) (μ.prod μ) := by
    exact hsum.sub (h11'.const_mul 2)
  have hprod20 : ∫ z : ℝ × ℝ, z.1 ^ 2 ∂μ.prod μ =
      (∫ x : ℝ, x ^ 2 ∂μ) * ∫ y : ℝ, (1 : ℝ) ∂μ := by
    convert integral_prod_mul (μ := μ) (ν := μ)
      (fun x : ℝ => x ^ 2) (fun _ : ℝ => (1 : ℝ)) using 1; simp
  have hprod02 : ∫ z : ℝ × ℝ, z.2 ^ 2 ∂μ.prod μ =
      (∫ x : ℝ, (1 : ℝ) ∂μ) * ∫ y : ℝ, y ^ 2 ∂μ := by
    convert integral_prod_mul (μ := μ) (ν := μ)
      (fun _ : ℝ => (1 : ℝ)) (fun y : ℝ => y ^ 2) using 1; simp
  have hprod11 : ∫ z : ℝ × ℝ, z.1 * z.2 ∂μ.prod μ =
      (∫ x : ℝ, x ∂μ) * ∫ y : ℝ, y ∂μ := by
    exact integral_prod_mul (μ := μ) (ν := μ) (fun x : ℝ => x) (fun y : ℝ => y)
  have hpoly : (fun z : ℝ × ℝ => (z.1 - z.2) ^ 2) =
      (fun z : ℝ × ℝ => z.1 ^ 2 + z.2 ^ 2 - 2 * (z.1 * z.2)) := by
    funext z
    ring
  change (∫ z : ℝ × ℝ, (z.1 - z.2) ^ 2 ∂μ.prod μ) = _
  rw [hpoly, integral_sub hsum (h11'.const_mul 2), integral_add h20' h02']
  rw [hprod20, hprod02, integral_const_mul, hprod11]
  have hraw2 : ∫ x : ℝ, x ^ 2 ∂μ =
      (n.descFactorial 2 : ℝ) * (p : ℝ) ^ 2 +
        (n.descFactorial 1 : ℝ) * (p : ℝ) := by
    simpa [μ] using binomial_raw_second n p
  have hraw1 : ∫ x : ℝ, x ∂μ = (n : ℝ) * (p : ℝ) := by
    have h := ProbabilityTheory.integral_of_hasLaw_binomial
      (P := Bin(ℝ, n, p)) (X := id) ProbabilityTheory.HasLaw.id
    simpa [μ] using h.trans (by ring)
  simp only [integral_const, probReal_univ, smul_eq_mul]
  rw [hraw2, hraw1]
  rw [Nat.cast_descFactorial_two, Nat.descFactorial_one]
  ring

private lemma binomial_difference_fourth (n : ℕ) (p : I) :
    ∫ z : ℝ × ℝ, (z.1 - z.2) ^ 4
        ∂(Bin(ℝ, n, p)).prod Bin(ℝ, n, p) =
      2 * (n : ℝ) * (p : ℝ) * (1 - (p : ℝ)) +
        12 * (n : ℝ) * ((n : ℝ) - 1) *
          ((p : ℝ) * (1 - (p : ℝ))) ^ 2 := by
  let μ : Measure ℝ := Bin(ℝ, n, p)
  have hpow (r : ℕ) : Integrable (fun x : ℝ => x ^ r) μ := by
    simpa [μ] using (ProbabilityTheory.integrable_map_cast_binomial
      (n := n) (p := p) (fun x : ℝ => x ^ r))
  have h40 : Integrable (fun z : ℝ × ℝ => z.1 ^ 4 * (1 : ℝ)) (μ.prod μ) :=
    (hpow 4).mul_prod (integrable_const (1 : ℝ))
  have h04 : Integrable (fun z : ℝ × ℝ => (1 : ℝ) * z.2 ^ 4) (μ.prod μ) :=
    (integrable_const (1 : ℝ)).mul_prod (hpow 4)
  have h22 : Integrable (fun z : ℝ × ℝ => z.1 ^ 2 * z.2 ^ 2) (μ.prod μ) :=
    (hpow 2).mul_prod (hpow 2)
  have h31 : Integrable (fun z : ℝ × ℝ => z.1 ^ 3 * z.2 ^ 1) (μ.prod μ) :=
    (hpow 3).mul_prod (hpow 1)
  have h13 : Integrable (fun z : ℝ × ℝ => z.1 ^ 1 * z.2 ^ 3) (μ.prod μ) :=
    (hpow 1).mul_prod (hpow 3)
  have h40' : Integrable (fun z : ℝ × ℝ => z.1 ^ 4) (μ.prod μ) := by simpa using h40
  have h04' : Integrable (fun z : ℝ × ℝ => z.2 ^ 4) (μ.prod μ) := by simpa using h04
  have h22' : Integrable (fun z : ℝ × ℝ => z.1 ^ 2 * z.2 ^ 2) (μ.prod μ) := by
    simpa using h22
  have h31' : Integrable (fun z : ℝ × ℝ => z.1 ^ 3 * z.2) (μ.prod μ) := by
    simpa using h31
  have h13' : Integrable (fun z : ℝ × ℝ => z.1 * z.2 ^ 3) (μ.prod μ) := by
    simpa using h13
  have hpoly : (fun z : ℝ × ℝ => (z.1 - z.2) ^ 4) =
      (fun z : ℝ × ℝ => z.1 ^ 4 + z.2 ^ 4 + 6 * (z.1 ^ 2 * z.2 ^ 2) -
        4 * (z.1 ^ 3 * z.2) - 4 * (z.1 * z.2 ^ 3)) := by
    funext z
    ring
  have hsum1 : Integrable (fun z : ℝ × ℝ => z.1 ^ 4 + z.2 ^ 4) (μ.prod μ) :=
    h40'.add h04'
  have hsum2 : Integrable
      (fun z : ℝ × ℝ => z.1 ^ 4 + z.2 ^ 4 + 6 * (z.1 ^ 2 * z.2 ^ 2)) (μ.prod μ) :=
    hsum1.add (h22'.const_mul 6)
  have hsum3 : Integrable
      (fun z : ℝ × ℝ => z.1 ^ 4 + z.2 ^ 4 + 6 * (z.1 ^ 2 * z.2 ^ 2) -
        4 * (z.1 ^ 3 * z.2)) (μ.prod μ) := hsum2.sub (h31'.const_mul 4)
  have hsum4 : Integrable
      (fun z : ℝ × ℝ => z.1 ^ 4 + z.2 ^ 4 + 6 * (z.1 ^ 2 * z.2 ^ 2) -
        4 * (z.1 ^ 3 * z.2) - 4 * (z.1 * z.2 ^ 3)) (μ.prod μ) :=
    hsum3.sub (h13'.const_mul 4)
  have hprod40 : ∫ z : ℝ × ℝ, z.1 ^ 4 ∂μ.prod μ =
      (∫ x : ℝ, x ^ 4 ∂μ) * ∫ _ : ℝ, (1 : ℝ) ∂μ := by
    convert integral_prod_mul (μ := μ) (ν := μ)
      (fun x : ℝ => x ^ 4) (fun _ : ℝ => (1 : ℝ)) using 1; simp
  have hprod04 : ∫ z : ℝ × ℝ, z.2 ^ 4 ∂μ.prod μ =
      (∫ _ : ℝ, (1 : ℝ) ∂μ) * ∫ y : ℝ, y ^ 4 ∂μ := by
    convert integral_prod_mul (μ := μ) (ν := μ)
      (fun _ : ℝ => (1 : ℝ)) (fun y : ℝ => y ^ 4) using 1; simp
  have hprod22 : ∫ z : ℝ × ℝ, z.1 ^ 2 * z.2 ^ 2 ∂μ.prod μ =
      (∫ x : ℝ, x ^ 2 ∂μ) * ∫ y : ℝ, y ^ 2 ∂μ := by
    exact integral_prod_mul (μ := μ) (ν := μ)
      (fun x : ℝ => x ^ 2) (fun y : ℝ => y ^ 2)
  have hprod31 : ∫ z : ℝ × ℝ, z.1 ^ 3 * z.2 ∂μ.prod μ =
      (∫ x : ℝ, x ^ 3 ∂μ) * ∫ y : ℝ, y ∂μ := by
    convert integral_prod_mul (μ := μ) (ν := μ)
      (fun x : ℝ => x ^ 3) (fun y : ℝ => y) using 1
  have hprod13 : ∫ z : ℝ × ℝ, z.1 * z.2 ^ 3 ∂μ.prod μ =
      (∫ x : ℝ, x ∂μ) * ∫ y : ℝ, y ^ 3 ∂μ := by
    convert integral_prod_mul (μ := μ) (ν := μ)
      (fun x : ℝ => x) (fun y : ℝ => y ^ 3) using 1
  have hraw1 : ∫ x : ℝ, x ∂μ = (n : ℝ) * (p : ℝ) := by
    have h := ProbabilityTheory.integral_of_hasLaw_binomial
      (P := Bin(ℝ, n, p)) (X := id) ProbabilityTheory.HasLaw.id
    simpa [μ] using h.trans (by ring)
  have hraw2 : ∫ x : ℝ, x ^ 2 ∂μ =
      (n.descFactorial 2 : ℝ) * (p : ℝ) ^ 2 +
        (n.descFactorial 1 : ℝ) * (p : ℝ) := by
    simpa [μ] using binomial_raw_second n p
  have hraw3 : ∫ x : ℝ, x ^ 3 ∂μ =
      (n.descFactorial 3 : ℝ) * (p : ℝ) ^ 3 +
        3 * (n.descFactorial 2 : ℝ) * (p : ℝ) ^ 2 +
        (n.descFactorial 1 : ℝ) * (p : ℝ) := by
    simpa [μ] using binomial_raw_third n p
  have hraw4 : ∫ x : ℝ, x ^ 4 ∂μ =
      (n.descFactorial 4 : ℝ) * (p : ℝ) ^ 4 +
        6 * (n.descFactorial 3 : ℝ) * (p : ℝ) ^ 3 +
        7 * (n.descFactorial 2 : ℝ) * (p : ℝ) ^ 2 +
        (n.descFactorial 1 : ℝ) * (p : ℝ) := by
    simpa [μ] using binomial_raw_fourth n p
  change (∫ z : ℝ × ℝ, (z.1 - z.2) ^ 4 ∂μ.prod μ) = _
  rw [hpoly, integral_sub hsum3 (h13'.const_mul 4),
    integral_sub hsum2 (h31'.const_mul 4),
    integral_add hsum1 (h22'.const_mul 6), integral_add h40' h04',
    integral_const_mul, integral_const_mul, integral_const_mul]
  rw [hprod40, hprod04, hprod22, hprod31, hprod13]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, mul_one]
  rw [hraw1, hraw2, hraw3, hraw4]
  rw [Nat.cast_descFactorial_two, Nat.descFactorial_one]
  have hdf3 : (n.descFactorial 3 : ℝ) =
      (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) := by
    by_cases hn2 : 2 ≤ n
    · have hcast2 : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
        rw [Nat.cast_sub hn2]
        norm_num
      rw [show (3 : ℕ) = 2 + 1 by norm_num, Nat.descFactorial_succ]
      push_cast
      rw [Nat.cast_descFactorial_two, hcast2]
      ring
    · have hlt2 : n < 2 := Nat.lt_of_not_ge hn2
      interval_cases n <;> norm_num [Nat.descFactorial]
  have hdf4 : (n.descFactorial 4 : ℝ) =
      (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) * ((n : ℝ) - 3) := by
    by_cases hn3 : 3 ≤ n
    · have hcast3 : ((n - 3 : ℕ) : ℝ) = (n : ℝ) - 3 := by
        rw [Nat.cast_sub hn3]
        norm_num
      rw [show (4 : ℕ) = 3 + 1 by norm_num, Nat.descFactorial_succ]
      push_cast
      rw [hdf3, hcast3]
      ring
    · have hlt3 : n < 3 := Nat.lt_of_not_ge hn3
      interval_cases n <;> norm_num [Nat.descFactorial]
  rw [hdf3, hdf4]
  ring_nf

/-- Exact second moment of the difference of two independent binomial counts. -/
theorem binomial_difference_second_moment (n : ℕ) (p : I) :
    ∫ z : ℝ × ℝ, (z.1 - z.2) ^ 2
        ∂(Bin(ℝ, n, p)).prod Bin(ℝ, n, p) =
      2 * (n : ℝ) * (p : ℝ) * (1 - (p : ℝ)) :=
  binomial_difference_second n p

/-- Exact fourth moment of the difference of two independent binomial counts. -/
theorem binomial_difference_fourth_moment (n : ℕ) (p : I) :
    ∫ z : ℝ × ℝ, (z.1 - z.2) ^ 4
        ∂(Bin(ℝ, n, p)).prod Bin(ℝ, n, p) =
      2 * (n : ℝ) * (p : ℝ) * (1 - (p : ℝ)) +
        12 * (n : ℝ) * ((n : ℝ) - 1) *
          ((p : ℝ) * (1 - (p : ℝ))) ^ 2 :=
  binomial_difference_fourth n p

/-- The exact second moment is bounded by twice the binomial mean. -/
theorem binomial_difference_second_moment_le (n : ℕ) (p : I) :
    ∫ z : ℝ × ℝ, (z.1 - z.2) ^ 2
        ∂(Bin(ℝ, n, p)).prod Bin(ℝ, n, p) ≤
      2 * ((n : ℝ) * (p : ℝ)) := by
  rw [binomial_difference_second_moment]
  have hn : 0 ≤ (n : ℝ) := by positivity
  have hp0 : 0 ≤ (p : ℝ) := p.2.1
  have hp1 : (p : ℝ) ≤ 1 := p.2.2
  have hq : 1 - (p : ℝ) ≤ 1 := sub_le_self _ hp0
  have hpq : (p : ℝ) * (1 - (p : ℝ)) ≤ (p : ℝ) := by
    simpa using (mul_le_mul_of_nonneg_left
      (sub_le_self (1 : ℝ) hp0) hp0)
  have hmean : (n : ℝ) * (p : ℝ) * (1 - (p : ℝ)) ≤
      (n : ℝ) * (p : ℝ) := by
    simpa [mul_assoc] using (mul_le_mul_of_nonneg_left hpq hn)
  nlinarith

/-- The exact fourth moment is bounded by `2 λ + 12 λ²`, where `λ = n p`. -/
theorem binomial_difference_fourth_moment_le (n : ℕ) (p : I) :
    ∫ z : ℝ × ℝ, (z.1 - z.2) ^ 4
        ∂(Bin(ℝ, n, p)).prod Bin(ℝ, n, p) ≤
      2 * ((n : ℝ) * (p : ℝ)) + 12 * ((n : ℝ) * (p : ℝ)) ^ 2 := by
  rw [binomial_difference_fourth_moment]
  have hn : 0 ≤ (n : ℝ) := by positivity
  have hp0 : 0 ≤ (p : ℝ) := p.2.1
  have hp1 : (p : ℝ) ≤ 1 := p.2.2
  have hq0 : 0 ≤ 1 - (p : ℝ) := sub_nonneg.mpr hp1
  have hq : (p : ℝ) * (1 - (p : ℝ)) ≤ (p : ℝ) := by
    simpa using (mul_le_mul_of_nonneg_left
      (sub_le_self (1 : ℝ) hp0) hp0)
  have hq2 : ((p : ℝ) * (1 - (p : ℝ))) ^ 2 ≤ (p : ℝ) ^ 2 :=
    (sq_le_sq₀ (mul_nonneg hp0 hq0) hp0).2 hq
  have hnn : (n : ℝ) * ((n : ℝ) - 1) ≤ (n : ℝ) * (n : ℝ) := by
    apply mul_le_mul_of_nonneg_left
    linarith
    exact hn
  have hprod : (n : ℝ) * ((n : ℝ) - 1) *
        ((p : ℝ) * (1 - (p : ℝ))) ^ 2 ≤
      ((n : ℝ) * (n : ℝ)) * (p : ℝ) ^ 2 := by
    calc
      (n : ℝ) * ((n : ℝ) - 1) *
          ((p : ℝ) * (1 - (p : ℝ))) ^ 2 ≤
          ((n : ℝ) * (n : ℝ)) *
            ((p : ℝ) * (1 - (p : ℝ))) ^ 2 := by
        exact mul_le_mul_of_nonneg_right hnn (sq_nonneg _)
      _ ≤ ((n : ℝ) * (n : ℝ)) * (p : ℝ) ^ 2 := by
        exact mul_le_mul_of_nonneg_left hq2 (mul_nonneg hn hn)
  nlinarith

/-! ## A reusable third-moment interpolation layer -/

/--
The third absolute moment is controlled by the second and fourth moments.  This is the
elementary `L²` interpolation inequality written in a form that does not require a
separate moment API: the proof uses the scalar AM--GM inequality with
`c = sqrt (B / A)`, followed by integration.  In particular, once the binomial second
and fourth central-moment identities are supplied, this yields the usual
`O(λ^(3/2) + λ)` estimate without an unproved interface.
-/
theorem integral_abs_pow_three_le_sqrt_mul
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {D : Ω → ℝ}
    (hD2 : Integrable (fun ω => D ω ^ 2) μ)
    (hD3 : Integrable (fun ω => |D ω| ^ 3) μ)
    (hD4 : Integrable (fun ω => D ω ^ 4) μ) :
    ∫ ω, |D ω| ^ 3 ∂μ ≤
      Real.sqrt ((∫ ω, D ω ^ 2 ∂μ) * (∫ ω, D ω ^ 4 ∂μ)) := by
  let A : ℝ := ∫ ω, D ω ^ 2 ∂μ
  let B : ℝ := ∫ ω, D ω ^ 4 ∂μ
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact integral_nonneg (fun ω => sq_nonneg (D ω))
  have hB0 : 0 ≤ B := by
    dsimp [B]
    exact integral_nonneg (fun ω => by positivity)
  by_cases hA : A = 0
  · have hsq : (fun ω => D ω ^ 2) =ᵐ[μ] 0 := by
      apply (integral_eq_zero_iff_of_nonneg_ae
        (ae_of_all _ fun ω => sq_nonneg (D ω)) hD2).mp
      exact hA
    have hD0 : D =ᵐ[μ] 0 := hsq.mono fun ω hω => by
      simp only [Pi.zero_apply] at hω
      exact sq_eq_zero_iff.mp hω
    have hzero : (fun ω => |D ω| ^ 3) =ᵐ[μ] 0 :=
      hD0.mono fun ω hω => by simp [hω]
    rw [integral_eq_zero_of_ae hzero]
    exact Real.sqrt_nonneg _
  · have hApos : 0 < A := lt_of_le_of_ne hA0 (Ne.symm hA)
    have hBpos : 0 < B := by
      by_contra hB
      have hB' : B = 0 := le_antisymm (le_of_not_gt hB) hB0
      have hfour : (fun ω => D ω ^ 4) =ᵐ[μ] 0 := by
        apply (integral_eq_zero_iff_of_nonneg_ae
          (ae_of_all _ fun ω => by positivity) hD4).mp
        exact hB'
      have hD0 : D =ᵐ[μ] 0 := hfour.mono fun ω hω => by
        simp only [Pi.zero_apply] at hω
        exact (pow_eq_zero_iff (by norm_num)).mp hω
      have hsqzero : A = 0 := by
        dsimp [A]
        rw [integral_eq_zero_of_ae (hD0.mono fun ω hω => by simp [hω])]
      exact hA hsqzero
    let c : ℝ := Real.sqrt (B / A)
    have hc : 0 < c := by
      dsimp [c]
      exact Real.sqrt_pos.2 (div_pos hBpos hApos)
    have hpoint : ∀ ω, 2 * |D ω| ^ 3 ≤ c * D ω ^ 2 + c⁻¹ * D ω ^ 4 := by
      intro ω
      have hs : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
      have hc_sq' : (Real.sqrt c) ^ 2 = c := Real.sq_sqrt hc.le
      have hc4 : (Real.sqrt c) ^ 4 = c ^ 2 := by
        calc
          (Real.sqrt c) ^ 4 = ((Real.sqrt c) ^ 2) ^ 2 := by ring
          _ = c ^ 2 := by rw [hc_sq']
      have hx2 : |D ω| ^ 2 = D ω ^ 2 := sq_abs _
      have h := two_mul_le_add_sq (Real.sqrt c * |D ω|)
        (|D ω| ^ 2 / Real.sqrt c)
      calc
        2 * |D ω| ^ 3 = 2 * (Real.sqrt c * |D ω|) *
            (|D ω| ^ 2 / Real.sqrt c) := by field_simp [ne_of_gt hs]
        _ ≤ (Real.sqrt c * |D ω|) ^ 2 +
            (|D ω| ^ 2 / Real.sqrt c) ^ 2 := h
        _ = c * D ω ^ 2 + c⁻¹ * D ω ^ 4 := by
          field_simp [ne_of_gt hs]
          rw [hc4, hx2, hc_sq']
          ring
    have hleft : Integrable (fun ω => 2 * |D ω| ^ 3) μ := hD3.const_mul _
    have hright : Integrable (fun ω => c * D ω ^ 2 + c⁻¹ * D ω ^ 4) μ :=
      (hD2.const_mul _).add (hD4.const_mul _)
    have hint := integral_mono_ae hleft hright (ae_of_all _ hpoint)
    calc
      ∫ ω, |D ω| ^ 3 ∂μ = (2 : ℝ)⁻¹ * ∫ ω, 2 * |D ω| ^ 3 ∂μ := by
        rw [integral_const_mul]
        field_simp
      _ ≤ (2 : ℝ)⁻¹ * ∫ ω, (c * D ω ^ 2 + c⁻¹ * D ω ^ 4) ∂μ :=
        mul_le_mul_of_nonneg_left hint (by positivity)
      _ = (2 : ℝ)⁻¹ * (c * A + c⁻¹ * B) := by
        rw [integral_add (hD2.const_mul c) (hD4.const_mul c⁻¹),
          integral_const_mul, integral_const_mul]
      _ = Real.sqrt (A * B) := by
        have hc_ne : c ≠ 0 := ne_of_gt hc
        have hA_ne : A ≠ 0 := ne_of_gt hApos
        have hsqrtAB : Real.sqrt (A * B) = Real.sqrt A * Real.sqrt B := by
          rw [Real.sqrt_mul (le_of_lt hApos)]
        have hc_def : c = Real.sqrt B / Real.sqrt A := by
          dsimp [c]
          rw [Real.sqrt_div (le_of_lt hBpos)]
        rw [hc_def, hsqrtAB]
        have hsA : Real.sqrt A ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hApos)
        field_simp [hsA]
        rw [Real.sq_sqrt hApos.le, Real.sq_sqrt hBpos.le]
        ring

/--
The preceding interpolation bound applies directly to two independent binomial
coordinates.  This is the honest reusable conclusion available from the current
mathlib binomial API; the remaining sparse `λ` estimate is exactly the separate
second/fourth central-moment calculation.
-/
theorem binomial_difference_third_moment_le_sqrt_mul (n : ℕ) (p : I) :
    ∫ z : ℝ × ℝ, |z.1 - z.2| ^ 3
        ∂(Bin(ℝ, n, p)).prod Bin(ℝ, n, p) ≤
      Real.sqrt ((∫ z : ℝ × ℝ, (z.1 - z.2) ^ 2
          ∂(Bin(ℝ, n, p)).prod Bin(ℝ, n, p)) *
        (∫ z : ℝ × ℝ, (z.1 - z.2) ^ 4
          ∂(Bin(ℝ, n, p)).prod Bin(ℝ, n, p))) := by
  have h2 : Integrable (fun z : ℝ × ℝ => (z.1 - z.2) ^ 2)
      ((Bin(ℝ, n, p)).prod Bin(ℝ, n, p)) := by
    simpa only [sq_abs] using integrable_binomial_difference_pow n p 2
  have h4 : Integrable (fun z : ℝ × ℝ => (z.1 - z.2) ^ 4)
      ((Bin(ℝ, n, p)).prod Bin(ℝ, n, p)) := by
    have h4' := integrable_binomial_difference_pow n p 4
    convert h4' using 1
    funext z
    rw [show (4 : ℕ) = 2 * 2 by norm_num]
    simp only [pow_mul]
    rw [sq_abs]
  have h3 := integrable_binomial_difference_pow n p 3
  simpa using
    (integral_abs_pow_three_le_sqrt_mul
      (μ := (Bin(ℝ, n, p)).prod Bin(ℝ, n, p))
      (D := fun z : ℝ × ℝ => z.1 - z.2)
      h2 h3 h4)

/--
The preceding interpolation and the explicit second/fourth bounds give the sparse-scale
third-moment estimate.  The displayed form is `O(λ + λ^(3/2))`, with
`λ = n * p`; the coefficient `5` is a deliberately coarse numerical constant.
-/
theorem binomial_difference_third_moment_le_sparse (n : ℕ) (p : I) :
    ∫ z : ℝ × ℝ, |z.1 - z.2| ^ 3
        ∂(Bin(ℝ, n, p)).prod Bin(ℝ, n, p) ≤
      2 * ((n : ℝ) * (p : ℝ)) +
        5 * ((n : ℝ) * (p : ℝ)) *
          Real.sqrt ((n : ℝ) * (p : ℝ)) := by
  let lam : ℝ := (n : ℝ) * (p : ℝ)
  have hlam0 : 0 ≤ lam := by
    dsimp [lam]
    exact mul_nonneg (by positivity) p.2.1
  have h2 := binomial_difference_second_moment_le n p
  have h4 := binomial_difference_fourth_moment_le n p
  have h3 := binomial_difference_third_moment_le_sqrt_mul n p
  let A : ℝ := ∫ z : ℝ × ℝ, (z.1 - z.2) ^ 2
      ∂(Bin(ℝ, n, p)).prod Bin(ℝ, n, p)
  let B4 : ℝ := ∫ z : ℝ × ℝ, (z.1 - z.2) ^ 4
      ∂(Bin(ℝ, n, p)).prod Bin(ℝ, n, p)
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact integral_nonneg (fun z => sq_nonneg (z.1 - z.2))
  have hB40 : 0 ≤ B4 := by
    dsimp [B4]
    exact integral_nonneg (fun z => by positivity)
  have hprod : A * B4 ≤ (2 * lam) * (2 * lam + 12 * lam ^ 2) := by
    have h2' : A ≤ 2 * lam := by simpa [A, lam] using h2
    have h4' : B4 ≤ 2 * lam + 12 * lam ^ 2 := by simpa [B4, lam] using h4
    calc
      A * B4 ≤ (2 * lam) * B4 :=
        mul_le_mul_of_nonneg_right h2' hB40
      _ ≤ (2 * lam) * (2 * lam + 12 * lam ^ 2) := by
        exact mul_le_mul_of_nonneg_left h4' (by positivity)
  have hsqrt : Real.sqrt (A * B4) ≤
      Real.sqrt ((2 * lam) * (2 * lam + 12 * lam ^ 2)) :=
    Real.sqrt_le_sqrt hprod
  have hr0 : 0 ≤ Real.sqrt lam := Real.sqrt_nonneg _
  have hr2 : (Real.sqrt lam) ^ 2 = lam := Real.sq_sqrt hlam0
  have htarget : Real.sqrt ((2 * lam) * (2 * lam + 12 * lam ^ 2)) ≤
      2 * lam + 5 * lam * Real.sqrt lam := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · calc
        (2 * lam) * (2 * lam + 12 * lam ^ 2) =
            4 * lam ^ 2 + 24 * lam ^ 3 := by ring
        _ ≤ (2 * lam + 5 * lam * Real.sqrt lam) ^ 2 := by
          have hexpand : (2 * lam + 5 * lam * Real.sqrt lam) ^ 2 =
              4 * lam ^ 2 + 25 * lam ^ 2 * (Real.sqrt lam) ^ 2 +
                20 * lam ^ 2 * Real.sqrt lam := by ring
          rw [hexpand, hr2]
          have hlam3 : 0 ≤ lam ^ 3 := by positivity
          have hcross : 0 ≤ 20 * lam ^ 2 * Real.sqrt lam := by positivity
          nlinarith
  calc
    ∫ z : ℝ × ℝ, |z.1 - z.2| ^ 3
        ∂(Bin(ℝ, n, p)).prod Bin(ℝ, n, p) ≤ Real.sqrt (A * B4) := by
      simpa [A, B4] using h3
    _ ≤ Real.sqrt ((2 * lam) * (2 * lam + 12 * lam ^ 2)) := hsqrt
    _ ≤ 2 * lam + 5 * lam * Real.sqrt lam := htarget
    _ = 2 * ((n : ℝ) * (p : ℝ)) +
        5 * ((n : ℝ) * (p : ℝ)) *
          Real.sqrt ((n : ℝ) * (p : ℝ)) := by rfl

/--
An explicit mean-scale specialization: when `n * p = B` (in particular, `p = B / n`
when `n > 0`), the sparse bound is written directly in terms of `B`.
-/
theorem binomial_difference_third_moment_le_of_mean_eq
    (n : ℕ) (p : I) (B : ℝ)
    (hmean : (n : ℝ) * (p : ℝ) = B) :
    ∫ z : ℝ × ℝ, |z.1 - z.2| ^ 3
        ∂(Bin(ℝ, n, p)).prod Bin(ℝ, n, p) ≤
      2 * B + 5 * B * Real.sqrt B := by
  simpa [hmean] using binomial_difference_third_moment_le_sparse n p

end OTSelector.Feedback
